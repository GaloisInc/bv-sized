{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.Internal
Copyright   : (c) Benjamin Selfridge, 2018
                  Galois Inc.
License     : BSD3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a width-parameterized 'BitVector' type and various associated
operations that assume a 2's complement representation. This module exports more of
the internals of the type as well as several functions that operate on explicit
'NatRepr's instead of requiring a 'KnownNat' constraint.
-}

module Data.BitVector.Sized.Internal
  ( -- * BitVector type
    BitVector(..)
  , bv
    -- * Bitwise operations (width-preserving)
    -- | These are alternative versions of some of the 'Bits' functions where we do
    -- not need to know the width at compile time. They are all width-preserving.
  , bvAnd, bvOr, bvXor
  , bvComplement
  , bvShift, bvRotate
  , bvWidth
  , bvTestBit
  , bvPopCount
    -- * Arithmetic operations (width-preserving)
  , bvAdd, bvMul
  , bvAbs, bvNegate
  , bvSignum
    -- * Bitwise operations (variable width)
    -- | These are functions that involve bit vectors of different lengths.
  , bvConcat, (<:>)
  , bvExtract, bvExtractWithRepr
  , bvZext, bvZextWithRepr
  , bvSext, bvSextWithRepr
    -- * Conversions to Integer
  , bvIntegerU
  , bvIntegerS
  ) where

import Data.Bits
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import GHC.TypeLits
import Text.Printf
import Unsafe.Coerce (unsafeCoerce)
----------------------------------------
-- BitVector data type definitions

-- | BitVector datatype, parameterized by width.
data BitVector (w :: Nat) :: * where
  BV :: NatRepr w -> Integer -> BitVector w

-- | Construct a bit vector in a context where the width is inferrable from the type
-- context. The 'Integer' input (an unbounded data type, hence with an infinite-width
-- bit representation), whether positive or negative is silently truncated to fit
-- into the number of bits demanded by the return type.
--
-- >>> bv 0xA :: BitVector 4
-- 0xa<4>
-- >>> bv 0xA :: BitVector 3
-- 0x2<3>
-- >>> bv (-1) :: BitVector 8
-- 0xff<8>
-- >>> bv (-1) :: BitVector 32
-- 0xffffffff<32>

bv :: KnownNat w => Integer -> BitVector w
bv x = BV wRepr (truncBits width (fromIntegral x))
  where wRepr = knownNat
        width = natValue wRepr

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a (positive) Integer.
bvIntegerU :: BitVector w -> Integer
bvIntegerU (BV _ x) = x

-- | Signed interpretation of a bit vector as an Integer.
bvIntegerS :: BitVector w -> Integer
bvIntegerS bvec = case bvTestBit bvec (width - 1) of
  True  -> bvIntegerU bvec - (1 `shiftL` width)
  False -> bvIntegerU bvec
  where width = bvWidth bvec

----------------------------------------
-- BitVector w operations (fixed width)

-- | Bitwise and.
bvAnd :: BitVector w -> BitVector w -> BitVector w
bvAnd (BV wRepr x) (BV _ y) = BV wRepr (x .&. y)

-- | Bitwise or.
bvOr :: BitVector w -> BitVector w -> BitVector w
bvOr (BV wRepr x) (BV _ y) = BV wRepr (x .|. y)

-- | Bitwise xor.
bvXor :: BitVector w -> BitVector w -> BitVector w
bvXor (BV wRepr x) (BV _ y) = BV wRepr (x `xor` y)

-- | Bitwise complement (flip every bit).
bvComplement :: BitVector w -> BitVector w
bvComplement (BV wRepr x) = BV wRepr (truncBits width (complement x))
  where width = natValue wRepr

-- | Bitwise shift.
bvShift :: BitVector w -> Int -> BitVector w
bvShift bvec@(BV wRepr _) shf = BV wRepr (truncBits width (x `shift` shf))
  where width = natValue wRepr
        x     = bvIntegerS bvec -- arithmetic right shift when negative

-- | Bitwise rotate.
bvRotate :: BitVector w -> Int -> BitVector w
bvRotate bvec rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` (bvWidth bvec)
        leftChunk = bvShift bvec rot
        rightChunk = bvShift bvec (rot - bvWidth bvec)

-- | Get the width of a 'BitVector'.
bvWidth :: BitVector w -> Int
bvWidth (BV wRepr _) = fromIntegral (natValue wRepr)

-- | Test if a particular bit is set.
bvTestBit :: BitVector w -> Int -> Bool
bvTestBit (BV _ x) b = testBit x b

-- | Get the number of 1 bits in a 'BitVector'.
bvPopCount :: BitVector w -> Int
bvPopCount (BV _ x) = popCount x

----------------------------------------
-- BitVector w arithmetic operations (fixed width)

-- | Bitwise add.
bvAdd :: BitVector w -> BitVector w -> BitVector w
bvAdd (BV wRepr x) (BV _ y) = BV wRepr (truncBits width (x + y))
  where width = natValue wRepr

-- | Bitwise multiply.
bvMul :: BitVector w -> BitVector w -> BitVector w
bvMul (BV wRepr x) (BV _ y) = BV wRepr (truncBits width (x * y))
  where width = natValue wRepr

-- | Bitwise absolute value.
bvAbs :: BitVector w -> BitVector w
bvAbs bvec@(BV wRepr _) = BV wRepr abs_x
  where width = natValue wRepr
        x     = bvIntegerS bvec
        abs_x = truncBits width (abs x) -- this is necessary

-- | Bitwise negation.
bvNegate :: BitVector w -> BitVector w
bvNegate (BV wRepr x) = BV wRepr (truncBits width (-x))
  where width = fromIntegral (natValue wRepr) :: Integer

-- | Get the sign bit as a 'BitVector'.
bvSignum :: BitVector w -> BitVector w
bvSignum bvec@(BV wRepr _) = (bvShift bvec (1 - width)) `bvAnd` (BV wRepr 0x1)
  where width = fromIntegral (natValue wRepr)

----------------------------------------
-- Width-changing operations

-- | Concatenate two bit vectors.
--
-- >>> (bv 0xAA :: BitVector 8) `bvConcat` (bv 0xBCDEF0 :: BitVector 24)
-- 0xaabcdef0<32>
--
-- Note that the first argument gets placed in the higher-order bits. The above
-- example should be illustrative enough.
bvConcat :: BitVector v -> BitVector w -> BitVector (v+w)
bvConcat (BV hiWRepr hi) (BV loWRepr lo) =
  BV (hiWRepr `addNat` loWRepr) ((hi `shiftL` loWidth) .|. lo)
  where loWidth = fromIntegral (natValue loWRepr)

-- | Infix 'bvConcat'.
(<:>) :: BitVector v -> BitVector w -> BitVector (v+w)
(<:>) = bvConcat

infixl 6 <:>

-- | Slice out a smaller bit vector from a larger one. The lowest significant bit is
-- given explicitly as an argument of type 'Int', and the length of the slice is
-- inferred from a type-level context.
--
-- >>> bvExtract 12 (bv 0xAABCDEF0 :: BitVector 32) :: BitVector 8
-- 0xcd<8>
--
-- Note that 'bvExtract' does not do any bounds checking whatsoever; if you try and
-- extract bits that aren't present in the input, you will get 0's.
bvExtract :: forall w w' . (KnownNat w')
          => Int
          -> BitVector w
          -> BitVector w'
bvExtract pos bvec = bv xShf
  where (BV _ xShf) = bvShift bvec (- pos)

-- | Unconstrained variant of 'bvExtract' with an explicit 'NatRepr' argument.
bvExtractWithRepr :: NatRepr w'
                  -> Int
                  -> BitVector w
                  -> BitVector w'
bvExtractWithRepr repr pos bvec = BV repr xShf
  where (BV _ xShf) = bvShift bvec (- pos)

-- | Zero-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvZext :: forall w w' . KnownNat w'
       => BitVector w
       -> BitVector w'
bvZext (BV _ x) = bv x

-- | Unconstrained variant of 'bvZext' with an explicit 'NatRepr' argument.
bvZextWithRepr :: NatRepr w'
               -> BitVector w
               -> BitVector w'
bvZextWithRepr repr (BV _ x) = BV repr x

-- | Sign-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvSext :: forall w w' . KnownNat w'
       => BitVector w
       -> BitVector w'
bvSext bvec = bv (bvIntegerS bvec)

-- | Unconstrained variant of 'bvSext' with an explicit 'NatRepr' argument.
bvSextWithRepr :: NatRepr w'
               -> BitVector w
               -> BitVector w'
bvSextWithRepr repr bvec = BV repr (bvIntegerS bvec)

----------------------------------------
-- Class instances

instance Show (BitVector w) where
  show (BV wRepr val) = prettyHex width val
    where width = natValue wRepr

instance ShowF BitVector

instance Eq (BitVector w) where
  (BV _ x) == (BV _ y) = x == y

instance EqF BitVector where
  (BV _ x) `eqF` (BV _ y) = x == y

instance TestEquality BitVector where
  testEquality (BV wRepr x) (BV wRepr' y) =
    case natValue wRepr == natValue wRepr' && x == y of
      True  -> Just (unsafeCoerce (Refl :: a :~: a))
      False -> Nothing

instance KnownNat w => Bits (BitVector w) where
  (.&.)        = bvAnd
  (.|.)        = bvOr
  xor          = bvXor
  complement   = bvComplement
  shift        = bvShift
  rotate       = bvRotate
  bitSize      = bvWidth
  bitSizeMaybe = Just . bvWidth
  isSigned     = const False
  testBit      = bvTestBit
  bit          = bv . bit
  popCount     = bvPopCount

instance KnownNat w => FiniteBits (BitVector w) where
  finiteBitSize = bvWidth

instance KnownNat w => Num (BitVector w) where
  (+)         = bvAdd
  (*)         = bvMul
  abs         = bvAbs
  signum      = bvSignum
  fromInteger = bv
  negate      = bvNegate

instance KnownNat w => Enum (BitVector w) where
  toEnum   = bv . fromIntegral
  fromEnum = fromIntegral . bvIntegerU

instance KnownNat w => Bounded (BitVector w) where
  minBound = bv 0
  maxBound = bv (-1)

----------------------------------------
-- UTILITIES

----------------------------------------
-- Pretty Printing

-- | Print an integral value in hex with a leading "0x"
prettyHex :: (Integral a, PrintfArg a, Show a) => a -> Integer -> String
prettyHex width val = printf format val width
  where numDigits = (width+3) `div` 4
        format = "0x%." ++ show numDigits ++ "x<%d>"

----------------------------------------
-- Bits

-- | Mask for a specified number of lower bits.
lowMask :: (Integral a, Bits b) => a -> b
lowMask numBits = complement (complement zeroBits `shiftL` fromIntegral numBits)

-- | Truncate to a specified number of lower bits.
truncBits :: (Integral a, Bits b) => a -> b -> b
truncBits width b = b .&. lowMask width
