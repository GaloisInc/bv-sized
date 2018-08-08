{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized
Copyright   : (c) Galois Inc. 2018
License     : BSD3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a width-parameterized 'BitVector' type and various associated
operations that assume a 2's complement representation.
-}

module Data.BitVector.Sized
  ( -- * BitVector type
    BitVector(..)
  , bitVector
  , bv0
    -- * Bitwise operations (width-preserving)
    -- | These are alternative versions of some of the 'Bits' functions where we do
    -- not need to know the width at compile time. They are all width-preserving.
  , bvAnd, bvOr, bvXor
  , bvComplement
  , bvShift, bvShiftL, bvShiftRA, bvShiftRL, bvRotate
  , bvWidth
  , bvTestBit
  , bvPopCount
  , bvTruncBits
    -- * Arithmetic operations (width-preserving)
  , bvAdd, bvMul
  , bvQuotU, bvQuotS
  , bvRemU, bvRemS
  , bvAbs, bvNegate
  , bvSignum
  , bvLTS, bvLTU
    -- * Variable-width operations
    -- | These are functions that involve bit vectors of different lengths.
  , bvConcat, (<:>), bvConcatMany, bvConcatManyWithRepr
  , bvExtract, bvExtractWithRepr
  , bvZext, bvZextWithRepr
  , bvSext, bvSextWithRepr
    -- * Conversions to Integer
  , bvIntegerU
  , bvIntegerS
    -- * Byte decomposition
  , bvGetBytesU
  ) where

import Data.Bits
import Data.Ix
import Data.Parameterized
import GHC.TypeLits
import Numeric
import System.Random
import Test.QuickCheck (Arbitrary(..), choose)
import Text.PrettyPrint.HughesPJClass
import Text.Printf
import Unsafe.Coerce (unsafeCoerce)

----------------------------------------
-- BitVector data type definitions

-- | BitVector datatype, parameterized by width.
data BitVector (w :: Nat) :: * where
  BV :: NatRepr w -> Integer -> BitVector w

-- | Construct a bit vector with a particular width, where the width is inferrable
-- from the type context. The 'Integer' input (an unbounded data type, hence with an
-- infinite-width bit representation), whether positive or negative, is silently
-- truncated to fit into the number of bits demanded by the return type.
--
-- >>> bitVector 0xA :: BitVector 4
-- 0xa
-- >>> bitVector 0xA :: BitVector 2
-- 0x2
bitVector :: KnownNat w => Integer -> BitVector w
bitVector x = BV wRepr (truncBits width (fromIntegral x))
  where wRepr = knownNat
        width = natValue wRepr

-- | The zero bitvector with width 0.
bv0 :: BitVector 0
bv0 = bitVector 0

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a (positive) Integer.
bvIntegerU :: BitVector w -> Integer
bvIntegerU (BV _ x) = x

-- | Signed interpretation of a bit vector as an Integer.
bvIntegerS :: BitVector w -> Integer
bvIntegerS bv = if bvTestBit bv (width - 1)
                then bvIntegerU bv - (1 `shiftL` width)
                else bvIntegerU bv
  where width = bvWidth bv

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

-- | Bitwise shift. Uses an arithmetic right shift.
bvShift :: BitVector w -> Int -> BitVector w
bvShift bv@(BV wRepr _) shf = BV wRepr (truncBits width (x `shift` shf))
  where width = natValue wRepr
        x     = bvIntegerS bv -- arithmetic right shift when negative

toPos :: Int -> Int
toPos x | x < 0 = 0
toPos x = x

-- | Left shift.
bvShiftL :: BitVector w -> Int -> BitVector w
bvShiftL bv shf = bvShift bv (toPos shf)

-- | Right arithmetic shift.
bvShiftRA :: BitVector w -> Int -> BitVector w
bvShiftRA bv shf = bvShift bv (- (toPos shf))

-- | Right logical shift.
bvShiftRL :: BitVector w -> Int -> BitVector w
bvShiftRL bv@(BV wRepr _) shf = BV wRepr (truncBits width (x `shift` (- toPos shf)))
  where width = natValue wRepr
        x     = bvIntegerU bv

-- | Bitwise rotate.
bvRotate :: BitVector w -> Int -> BitVector w
bvRotate bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` bvWidth bv
        leftChunk = bvShift bv rot
        rightChunk = bvShift bv (rot - bvWidth bv)

-- | Get the width of a 'BitVector'.
bvWidth :: BitVector w -> Int
bvWidth (BV wRepr _) = fromIntegral (natValue wRepr)

-- | Test if a particular bit is set.
bvTestBit :: BitVector w -> Int -> Bool
bvTestBit (BV _ x) b = testBit x b

-- | Get the number of 1 bits in a 'BitVector'.
bvPopCount :: BitVector w -> Int
bvPopCount (BV _ x) = popCount x

-- | Truncate a bit vector to a particular width given at runtime, while keeping the
-- type-level width constant.
bvTruncBits :: BitVector w -> Int -> BitVector w
bvTruncBits (BV wRepr x) b = BV wRepr (truncBits b x)

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

-- | Bitwise division (unsigned). Rounds to zero.
bvQuotU :: BitVector w -> BitVector w -> BitVector w
bvQuotU (BV wRepr x) (BV _ y) = BV wRepr (x `quot` y)

-- | Bitwise division (signed). Rounds to zero (not negative infinity).
bvQuotS :: BitVector w -> BitVector w -> BitVector w
bvQuotS bv1@(BV wRepr _) bv2 = BV wRepr (truncBits width (x `quot` y))
  where x = bvIntegerS bv1
        y = bvIntegerS bv2
        width = natValue wRepr

-- | Bitwise remainder after division (unsigned), when rounded to zero.
bvRemU :: BitVector w -> BitVector w -> BitVector w
bvRemU (BV wRepr x) (BV _ y) = BV wRepr (x `rem` y)

-- | Bitwise remainder after  division (signed), when rounded to zero (not negative
-- infinity).
bvRemS :: BitVector w -> BitVector w -> BitVector w
bvRemS bv1@(BV wRepr _) bv2 = BV wRepr (truncBits width (x `rem` y))
  where x = bvIntegerS bv1
        y = bvIntegerS bv2
        width = natValue wRepr

-- | Bitwise absolute value.
bvAbs :: BitVector w -> BitVector w
bvAbs bv@(BV wRepr _) = BV wRepr abs_x
  where width = natValue wRepr
        x     = bvIntegerS bv
        abs_x = truncBits width (abs x) -- this is necessary

-- | Bitwise negation.
bvNegate :: BitVector w -> BitVector w
bvNegate (BV wRepr x) = BV wRepr (truncBits width (-x))
  where width = fromIntegral (natValue wRepr) :: Integer

-- | Get the sign bit as a 'BitVector'.
bvSignum :: BitVector w -> BitVector w
bvSignum bv@(BV wRepr _) = bvShift bv (1 - width) `bvAnd` BV wRepr 0x1
  where width = fromIntegral (natValue wRepr)

-- | Signed less than.
bvLTS :: BitVector w -> BitVector w -> Bool
bvLTS bv1 bv2 = bvIntegerS bv1 < bvIntegerS bv2

-- | Unsigned less than.
bvLTU :: BitVector w -> BitVector w -> Bool
bvLTU bv1 bv2 = bvIntegerU bv1 < bvIntegerU bv2

----------------------------------------
-- Width-changing operations

-- | Concatenate two bit vectors.
--
-- >>> (0xAA :: BitVector 8) `bvConcat` (0xBCDEF0 :: BitVector 24)
-- 0xaabcdef0
-- >>> :type it
-- it :: BitVector 32
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

bvConcatSome :: Some BitVector -> Some BitVector -> Some BitVector
bvConcatSome (Some bv1) (Some bv2) = Some (bv2 <:> bv1)

-- | Concatenate a list of 'BitVector's into a 'BitVector' of arbitrary width. The ordering is little endian:
--
-- >>> bvConcatMany [0xAA :: BitVector 8, 0xBB] :: BitVector 16
-- 0xbbaa
-- >>> bvConcatMany [0xAA :: BitVector 8, 0xBB, 0xCC] :: BitVector 16
-- 0xbbaa
--
-- If the sum of the widths of the input 'BitVector's exceeds the output width, we
-- ignore the tail end of the list.
bvConcatMany :: KnownNat w' => [BitVector w] -> BitVector w'
bvConcatMany = bvConcatManyWithRepr knownNat

-- | 'bvConcatMany' with an explicit 'NatRepr'.
bvConcatManyWithRepr :: NatRepr w' -> [BitVector w] -> BitVector w'
bvConcatManyWithRepr wRepr bvs =
  viewSome (bvZextWithRepr wRepr) $ foldl bvConcatSome (Some bv0) (Some <$> bvs)

infixl 6 <:>

-- | Slice out a smaller bit vector from a larger one. The lowest significant bit is
-- given explicitly as an argument of type 'Int', and the length of the slice is
-- inferred from a type-level context.
--
-- >>> bvExtract 12 (0xAABCDEF0 :: BitVector 32) :: BitVector 8
-- 0xcd
--
-- Note that 'bvExtract' does not do any bounds checking whatsoever; if you try and
-- extract bits that aren't present in the input, you will get 0's.
bvExtract :: forall w w' . (KnownNat w')
          => Int
          -> BitVector w
          -> BitVector w'
bvExtract pos bv = bitVector xShf
  where (BV _ xShf) = bvShift bv (- pos)

-- | Unconstrained variant of 'bvExtract' with an explicit 'NatRepr' argument.
bvExtractWithRepr :: NatRepr w'
                  -> Int
                  -> BitVector w
                  -> BitVector w'
bvExtractWithRepr repr pos bv = BV repr (truncBits width xShf)
  where (BV _ xShf) = bvShift bv (- pos)
        width = natValue repr

-- | Zero-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvZext :: forall w w' . KnownNat w'
       => BitVector w
       -> BitVector w'
bvZext (BV _ x) = bitVector x

-- | Unconstrained variant of 'bvZext' with an explicit 'NatRepr' argument.
bvZextWithRepr :: NatRepr w'
               -> BitVector w
               -> BitVector w'
bvZextWithRepr repr (BV _ x) = BV repr (truncBits width x)
  where width = natValue repr

-- | Sign-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvSext :: forall w w' . KnownNat w'
       => BitVector w
       -> BitVector w'
bvSext bv = bitVector (bvIntegerS bv)

-- | Unconstrained variant of 'bvSext' with an explicit 'NatRepr' argument.
bvSextWithRepr :: NatRepr w'
               -> BitVector w
               -> BitVector w'
bvSextWithRepr repr bv = BV repr (truncBits width (bvIntegerS bv))
  where width = natValue repr

----------------------------------------
-- Byte decomposition

-- | Given a 'BitVector' of arbitrary length, decompose it into a list of bytes. Uses
-- an unsigned interpretation of the input vector, so if you ask for more bytes that
-- the 'BitVector' contains, you get zeros. The result is little-endian, so the first
-- element of the list will be the least significant byte of the input vector.
bvGetBytesU :: Int -> BitVector w -> [BitVector 8]
bvGetBytesU n _ | n <= 0 = []
bvGetBytesU n bv = bvExtract 0 bv : bvGetBytesU (n-1) (bvShiftRL bv 8)

----------------------------------------
-- Bits

-- | Mask for a specified number of lower bits.
lowMask :: (Integral a, Bits b) => a -> b
lowMask numBits = complement (complement zeroBits `shiftL` fromIntegral numBits)

-- | Truncate to a specified number of lower bits.
truncBits :: (Integral a, Bits b) => a -> b -> b
truncBits width b = b .&. lowMask width

----------------------------------------
-- Class instances
$(return [])

instance Show (BitVector w) where
  show (BV _ x) = "0x" ++ showHex x ""

instance KnownNat w => Read (BitVector w) where
  readsPrec s =
    (fmap . fmap) (\(a,s') -> (bitVector a, s')) (readsPrec s :: ReadS Integer)

instance ShowF BitVector

instance Eq (BitVector w) where
  (BV _ x) == (BV _ y) = x == y

instance EqF BitVector where
  (BV _ x) `eqF` (BV _ y) = x == y

instance Ord (BitVector w) where
  (BV _ x) `compare` (BV _ y) = x `compare` y

instance OrdF BitVector where
  (BV xRepr x) `compareF` (BV yRepr y) =
    case xRepr `compareF` yRepr of
      EQF -> fromOrdering (x `compare` y)
      cmp -> cmp

instance TestEquality BitVector where
  testEquality (BV wRepr x) (BV wRepr' y) =
    if natValue wRepr == natValue wRepr' && x == y
    then Just (unsafeCoerce (Refl :: a :~: a))
    else Nothing

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
  bit          = bitVector . bit
  popCount     = bvPopCount

instance KnownNat w => FiniteBits (BitVector w) where
  finiteBitSize = bvWidth

instance KnownNat w => Num (BitVector w) where
  (+)         = bvAdd
  (*)         = bvMul
  abs         = bvAbs
  signum      = bvSignum
  fromInteger = bitVector
  negate      = bvNegate

instance KnownNat w => Enum (BitVector w) where
  toEnum   = bitVector . fromIntegral
  fromEnum = fromIntegral . bvIntegerU

instance KnownNat w => Ix (BitVector w) where
  range (lo, hi) = bitVector <$> [bvIntegerU lo .. bvIntegerU hi]
  index (lo, hi) bv = index (bvIntegerU lo, bvIntegerU hi) (bvIntegerU bv)
  inRange (lo, hi) bv = inRange (bvIntegerU lo, bvIntegerU hi) (bvIntegerU bv)

instance KnownNat w => Bounded (BitVector w) where
  minBound = bitVector 0
  maxBound = bitVector (-1)

instance KnownNat w => Arbitrary (BitVector w) where
  arbitrary = choose (minBound, maxBound)

instance KnownNat w => Random (BitVector w) where
  randomR (bvLo, bvHi) gen =
    let (x, gen') = randomR (bvIntegerU bvLo, bvIntegerU bvHi) gen
    in (bitVector x, gen')
  random gen =
    let (x, gen') = random gen
    in (bitVector x, gen')

prettyHex :: (Integral a, PrintfArg a, Show a) => a -> Integer -> String
prettyHex width val = printf format val width
  where numDigits = (width+3) `quot` 4
        format = "0x%." ++ show numDigits ++ "x<%d>"

instance Pretty (BitVector w) where
  -- | Pretty print a bit vector (shows its width)
  pPrint (BV wRepr x) = text $ prettyHex (natValue wRepr) x
