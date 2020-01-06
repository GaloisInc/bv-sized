{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a width-parameterized 'BV' type and various
associated operations that assume a 2's complement representation.
-}

module Data.BitVector.Sized.Internal where

import Data.Bits
import Data.Parameterized
import GHC.Generics
import GHC.TypeLits
import Numeric.Natural

----------------------------------------
-- BitVector data type definitions

-- | Bitvector datatype, parameterized by width.
data BV (w :: Nat) :: * where
  BV :: Natural -> BV w
  deriving (Generic, Show, Read, Eq, Ord)

instance ShowF BV

instance EqF BV where
  BV bv `eqF` BV bv' = bv == bv'

-- | Construct a bit vector with a particular width, where the width
-- is provided as an explicit `NatRepr` argument. The input (an
-- unbounded data type, hence with an infinite-width bit
-- representation), whether positive or negative, is silently
-- truncated to fit into the number of bits demanded by the return
-- type.
--
-- >>> mkBV (knownNat @4) 0xA
-- 0xa
-- >>> mkBV (knownNat @2) 0xA
-- 0x2
mkBV :: NatRepr w -> Natural -> BV w
mkBV wRepr x = BV (truncBits width x)
  where width = natValue wRepr

-- | Construct a bit vector from an 'Integer'. The input is silently
-- truncated to the given width.
mkBVFromInteger :: NatRepr w -> Integer -> BV w
mkBVFromInteger wRepr x = mkBV wRepr (integerToNatural (natValue wRepr) x)

-- | The zero bitvector with width 0.
bv0 :: BV 0
bv0 = mkBV knownNat 0

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a Natural.
bvNatural :: BV w -> Natural
bvNatural (BV x) = x

-- | Signed interpretation of a bit vector as an Integer.
bvInteger :: NatRepr w -> BV w -> Integer
bvInteger wRepr (BV x) =
  if testBit x (width - 1)
  then fromIntegral x - (1 `shiftL` width)
  else fromIntegral x
  where width = fromIntegral (natValue wRepr)

----------------------------------------
-- BV w operations (fixed width)

-- | Bitwise and.
bvAnd :: BV w -> BV w -> BV w
bvAnd (BV x) (BV y) = BV (x .&. y)

-- | Bitwise or.
bvOr :: BV w -> BV w -> BV w
bvOr (BV x) (BV y) = BV (x .|. y)

-- | Bitwise xor.
bvXor :: BV w -> BV w -> BV w
bvXor (BV x) (BV y) = BV (x `xor` y)

-- FIXME: test this implementation.
-- | Bitwise complement (flip every bit).
bvComplement :: NatRepr w -> BV w -> BV w
bvComplement wRepr (BV x) =
  -- Convert to an integer, flip the bits, truncate to the appropriate
  -- width, and convert back to a natural.
  BV (integerToNatural width (complement (toInteger x)))
  where width = natValue wRepr

-- | Bitwise shift. Uses an arithmetic right shift.
bvShift :: NatRepr w -> BV w -> Int -> BV w
bvShift wRepr bv shf = BV (integerToNatural width (x `shift` shf))
  where width = natValue wRepr
        x     = bvInteger wRepr bv -- arithmetic right shift when negative

toPos :: Int -> Int
toPos x | x < 0 = 0
toPos x = x

-- | Left shift.
bvShiftL :: NatRepr w -> BV w -> Int -> BV w
bvShiftL wRepr (BV x) shf =
  -- Shift left by amount, then truncate.
  BV (truncBits width (x `shiftL` toPos shf))
  where width = natValue wRepr

-- | Right arithmetic shift.
bvShiftRA :: NatRepr w -> BV w -> Int -> BV w
bvShiftRA wRepr bv shf =
  -- Convert to an integer, shift right (arithmetic by default), then
  -- convert back to a natural with the correct width.
  BV (integerToNatural width (bvInteger wRepr bv `shiftR` toPos shf))
  where width = natValue wRepr

-- FIXME: test this
-- | Right logical shift.
bvShiftRL :: BV w -> Int -> BV w
bvShiftRL (BV x) shf =
  -- Shift right (logical by default on Naturals). No need to truncate bits.
  BV (x `shiftR` toPos shf)

-- FIXME: test this
-- | Bitwise rotate.
bvRotate :: NatRepr w -> BV w -> Int -> BV w
bvRotate wRepr bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` width
        leftChunk = bvShift wRepr bv rot
        rightChunk = bvShift wRepr bv (rot - width)
        width = fromIntegral (natValue wRepr)

-- | Test if a particular bit is set.
bvTestBit :: BV w -> Int -> Bool
bvTestBit (BV x) b = testBit x b

-- | Get the number of 1 bits in a 'BV'.
bvPopCount :: BV w -> Int
bvPopCount (BV x) = popCount x

-- | Truncate a bit vector to a particular width given at runtime,
-- while keeping the type-level width constant.
bvTruncBits :: BV w -> Int -> BV w
bvTruncBits (BV x) b = BV (truncBits b x)

----------------------------------------
-- BV w arithmetic operations (fixed width)

-- | Bitwise add.
bvAdd :: NatRepr w -> BV w -> BV w -> BV w
bvAdd wRepr (BV x) (BV y) = BV (truncBits width (x + y))
  where width = natValue wRepr

-- | Bitwise multiply.
bvMul :: NatRepr w -> BV w -> BV w -> BV w
bvMul wRepr (BV x) (BV y) = BV (truncBits width (x * y))
  where width = natValue wRepr

-- | Bitwise division (unsigned). Rounds to zero.
bvQuotU :: BV w -> BV w -> BV w
bvQuotU (BV x) (BV y) = BV (x `quot` y)

-- | Bitwise division (signed). Rounds to zero (not negative infinity).
bvQuotS :: NatRepr w -> BV w -> BV w -> BV w
bvQuotS wRepr bv1@(BV _) bv2 = BV (integerToNatural width (x `quot` y))
  where x = bvInteger wRepr bv1
        y = bvInteger wRepr bv2
        width = natValue wRepr

-- | Bitwise remainder after division (unsigned), when rounded to
-- zero.
bvRemU :: BV w -> BV w -> BV w
bvRemU (BV x) (BV y) = BV (x `rem` y)

-- | Bitwise remainder after division (signed), when rounded to zero
-- (not negative infinity).
bvRemS :: NatRepr w -> BV w -> BV w -> BV w
bvRemS wRepr bv1@(BV _) bv2 = BV (integerToNatural width (x `rem` y))
  where x = bvInteger wRepr bv1
        y = bvInteger wRepr bv2
        width = natValue wRepr

-- | Bitwise absolute value.
bvAbs :: NatRepr w -> BV w -> BV w
bvAbs wRepr bv@(BV _) = BV abs_x
  where width = natValue wRepr
        x     = bvInteger wRepr bv
        abs_x = integerToNatural width (abs x) -- this is necessary

-- | Bitwise negation.
bvNegate :: NatRepr w -> BV w -> BV w
bvNegate wRepr (BV x) = BV (truncBits width (-x))
  where width = fromIntegral (natValue wRepr) :: Integer

-- | Get the sign bit as a 'BV'.
bvSignum :: NatRepr w -> BV w -> BV w
bvSignum wRepr bv@(BV _) = bvShift wRepr bv (1 - width) `bvAnd` BV 0x1
  where width = fromIntegral (natValue wRepr)

-- | Signed less than.
bvLTS :: NatRepr w -> BV w -> BV w -> Bool
bvLTS wRepr bv1 bv2 = bvInteger wRepr bv1 < bvInteger wRepr bv2

-- | Unsigned less than.
bvLTU :: BV w -> BV w -> Bool
bvLTU bv1 bv2 = bvNatural bv1 < bvNatural bv2

----------------------------------------
-- Width-changing operations

-- | Concatenate two bit vectors.
--
-- >>> (0xAA :: BV 8) `bvConcat` (0xBCDEF0 :: BV 24)
-- 0xaabcdef0
-- >>> :type it
-- it :: BV 32
--
-- Note that the first argument gets placed in the higher-order
-- bits. The above example should be illustrative enough.
bvConcat :: NatRepr w -> BV v -> BV w -> BV (v+w)
bvConcat loWRepr (BV hi) (BV lo) =
  BV ((hi `shiftL` loWidth) .|. lo)
  where loWidth = fromIntegral (natValue loWRepr)

-- | Slice out a smaller bit vector from a larger one. The lowest
-- significant bit is given explicitly as an argument of type 'Int',
-- and the length of the slice is inferred from a type-level context.
--
-- >>> bvExtract 12 (0xAABCDEF0 :: BV 32) :: BV 8
-- 0xcd
--
-- Note that 'bvExtract' does not do any bounds checking whatsoever;
-- if you try and extract bits that aren't present in the input, you
-- will get 0's.
bvExtract :: NatRepr w
          -> NatRepr w'
          -> Int
          -> BV w
          -> BV w'
bvExtract wRepr wRepr' pos bv = mkBV wRepr' xShf
  where (BV xShf) = bvShift wRepr bv (- pos)

-- | Zero-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvZext :: NatRepr w'
       -> BV w
       -> BV w'
bvZext wRepr' (BV x) = BV (truncBits width x)
  where width = natValue wRepr'

-- | Sign-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvSext :: NatRepr w
       -> NatRepr w'
       -> BV w
       -> BV w'
bvSext wRepr wRepr' bv = mkBV wRepr' (integerToNatural width (bvInteger wRepr bv))
  where width = natValue wRepr'

----------------------------------------
-- Bits

-- | Mask for a specified number of lower bits.
lowMask :: (Integral a, Bits b) => a -> b
lowMask numBits = complement (complement zeroBits `shiftL` fromIntegral numBits)

-- | Truncate to a specified number of lower bits.
truncBits :: (Integral a, Bits b)
          => a
          -- ^ width to truncate to
          -> b
          -- ^ value to truncate
          -> b
truncBits width b = b .&. lowMask width

-- | Convert an Integer to a Natural safely by specifying the bit width.
integerToNatural :: Integral a
                 => a
                 -- ^ width
                 -> Integer
                 -> Natural
integerToNatural width x = fromIntegral (truncBits width x)
