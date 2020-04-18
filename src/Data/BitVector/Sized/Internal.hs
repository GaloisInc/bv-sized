{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
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
import Data.Parameterized hiding ( maxUnsigned )
import GHC.Generics
import GHC.TypeLits

----------------------------------------
-- BitVector data type definitions

-- | Bitvector datatype, parameterized by width.
data BV (w :: Nat) :: * where
  -- | We store the value as an 'Integer' rather than a 'Natural',
  -- since many of the operations on bitvectors rely on a two's
  -- complement representation. However, an invariant on the value is
  -- that it must always be positive.
  BV :: Integer -> BV w
  deriving (Generic, Show, Read, Eq, Ord)

instance ShowF BV

instance EqF BV where
  BV bv `eqF` BV bv' = bv == bv'

instance Hashable (BV w) where
  hashWithSalt salt (BV i) = hashWithSalt salt i

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
mkBV :: NatRepr w -> Integer -> BV w
mkBV wRepr x = BV (truncBits width x)
  where width = natValue wRepr

-- | The zero bitvector with width 0.
bv0 :: BV 0
bv0 = BV 0

-- | The 'BitVector' that has a particular bit set, and is 0 everywhere else.
bvBit :: (0 <= w', w' <= w) => NatRepr w -> NatRepr w' -> BV w
bvBit w ix = mkBV w (bit (fromIntegral (intValue ix)))

-- | The minimum unsigned value for bitvector with given width (always 0).
minUnsigned :: NatRepr w -> BV w
minUnsigned _ = BV 0

-- | The maximum unsigned value for bitvector with given width.
maxUnsigned :: NatRepr w -> BV w
maxUnsigned w = BV (bit (widthVal w) - 1)

-- | The minimum value for bitvector in two's complement with given width.
minSigned :: NatRepr w -> BV w
minSigned w = BV (negate (bit (widthVal w - 1)))

-- | The maximum value for bitvector in two's complement with given width.
maxSigned :: NatRepr w -> BV w
maxSigned w = BV (bit (widthVal w - 1) - 1)

toUnsigned :: NatRepr w -> Integer -> BV w
toUnsigned w i = BV (iMaxUnsigned .&. i)
  where BV iMaxUnsigned = maxUnsigned w

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a positive Integer.
bvIntegerUnsigned :: BV w -> Integer
bvIntegerUnsigned (BV x) = x

-- FIXME: In this, and other functions, we are converting to 'Int' in
-- order to use the underlying 'shiftL' function. This could be
-- problematic if the width is really huge.
-- | Signed interpretation of a bit vector as an Integer.
bvIntegerSigned :: NatRepr w -> BV w -> Integer
bvIntegerSigned wRepr (BV x) =
  if testBit x (width - 1)
  then x - (1 `shiftL` width)
  else x
  where width = fromIntegral (intValue wRepr)

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
  BV (truncBits width (complement x))
  where width = natValue wRepr

-- | Bitwise shift. Uses an arithmetic right shift.
bvShift :: NatRepr w -> BV w -> Int -> BV w
bvShift wRepr bv shf = BV (truncBits width (x `shift` shf))
  where width = natValue wRepr
        -- Convert the value to a signed integer so that we do an
        -- arithmetic right shift
        x     = bvIntegerSigned wRepr bv

toPos :: Int -> Int
toPos x | x < 0 = 0
toPos x = x

-- | Left shift.
bvShl :: NatRepr w -> BV w -> Int -> BV w
bvShl wRepr (BV x) shf =
  -- Shift left by amount, then truncate.
  BV (truncBits width (x `shiftL` toPos shf))
  where width = natValue wRepr

-- | Right arithmetic shift.
bvAshr :: NatRepr w -> BV w -> Int -> BV w
bvAshr wRepr bv shf =
  -- Convert to an integer, shift right (arithmetic by default), then
  -- convert back to a natural with the correct width.
  BV (truncBits width (bvIntegerSigned wRepr bv `shiftR` toPos shf))
  where width = natValue wRepr

-- FIXME: test this
-- | Right logical shift.
bvLshr :: BV w -> Int -> BV w
bvLshr (BV x) shf =
  -- Shift right (logical by default since the value is positive). No
  -- need to truncate bits, since the result is guaranteed to occupy
  -- no more bits than the input.
  BV (x `shiftR` toPos shf)

-- FIXME: test this
-- | Bitwise rotate.
bvRotate :: NatRepr w -> BV w -> Int -> BV w
bvRotate wRepr bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` width
        leftChunk = bvShift wRepr bv rot
        rightChunk = bvShift wRepr bv (rot - width)
        width = fromIntegral (intValue wRepr)

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

bvSub :: NatRepr w -> BV w -> BV w -> BV w
bvSub wRepr (BV x) (BV y) = BV (truncBits width (x - y))
  where width = natValue wRepr

-- | Bitwise multiply.
bvMul :: NatRepr w -> BV w -> BV w -> BV w
bvMul wRepr (BV x) (BV y) = BV (truncBits width (x * y))
  where width = natValue wRepr

-- | Bitwise division (unsigned). Rounds to zero.
bvUquot :: BV w -> BV w -> BV w
bvUquot (BV x) (BV y) = BV (x `quot` y)

-- | Bitwise division (signed). Rounds to zero (not negative infinity).
bvSquot :: NatRepr w -> BV w -> BV w -> BV w
bvSquot wRepr bv1@(BV _) bv2 = BV (truncBits width (x `quot` y))
  where x = bvIntegerSigned wRepr bv1
        y = bvIntegerSigned wRepr bv2
        width = natValue wRepr

-- | Bitwise remainder after division (unsigned), when rounded to
-- zero.
bvUrem :: BV w -> BV w -> BV w
bvUrem (BV x) (BV y) = BV (x `rem` y)

-- | Bitwise remainder after division (signed), when rounded to zero
-- (not negative infinity).
bvSrem :: NatRepr w -> BV w -> BV w -> BV w
bvSrem wRepr bv1@(BV _) bv2 = BV (truncBits width (x `rem` y))
  where x = bvIntegerSigned wRepr bv1
        y = bvIntegerSigned wRepr bv2
        width = natValue wRepr

-- | Bitwise absolute value.
bvAbs :: NatRepr w -> BV w -> BV w
bvAbs wRepr bv@(BV _) = BV abs_x
  where width = natValue wRepr
        x     = bvIntegerSigned wRepr bv
        abs_x = truncBits width (abs x) -- this is necessary

-- | Bitwise negation.
bvNegate :: NatRepr w -> BV w -> BV w
bvNegate wRepr (BV x) = BV (truncBits width (-x))
  where width = fromIntegral (natValue wRepr) :: Integer

-- | Get the sign bit as a 'BV'.
bvSignum :: NatRepr w -> BV w -> BV w
bvSignum wRepr bv@(BV _) = bvShift wRepr bv (1 - width) `bvAnd` BV 0x1
  where width = fromIntegral (natValue wRepr)

-- | Signed less than.
bvSlt :: NatRepr w -> BV w -> BV w -> Bool
bvSlt wRepr bv1 bv2 = bvIntegerSigned wRepr bv1 < bvIntegerSigned wRepr bv2

-- | Unsigned less than.
bvUlt :: BV w -> BV w -> Bool
bvUlt bv1 bv2 = bvIntegerUnsigned bv1 < bvIntegerUnsigned bv2

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
bvSext wRepr wRepr' bv = BV (truncBits width (bvIntegerSigned wRepr bv))
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
