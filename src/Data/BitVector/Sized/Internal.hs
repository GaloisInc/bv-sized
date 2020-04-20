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
import Data.Parameterized
import Data.Parameterized.WidthRepr
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

instance HashableF BV where
  hashWithSaltF salt (BV i) = hashWithSalt salt i

----------------------------------------
-- BitVector construction
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
mkBV :: WidthRepr w -> Integer -> BV w
mkBV w x = BV (x .&. widthMask w)

-- | The zero bitvector with width 0.
bv0 :: BV 0
bv0 = BV 0

-- | The 'BitVector' that has a particular bit set, and is 0
-- everywhere else.
bvBit :: (0 <= w', w' <= w) => WidthRepr w' -> BV w
bvBit ix = BV (bit (widthInt ix))

-- | Like 'bvBit', but without the requirement that the index bit
-- refers to an actual bit in the input 'BV'. If it is out of range,
-- just silently return 0.
bvBit' :: WidthRepr w -> Int -> BV w
bvBit' w ix = mkBV w (bit ix)

-- | The minimum unsigned value for bitvector with given width (always 0).
bvMinUnsigned :: BV w
bvMinUnsigned = BV 0

-- | The maximum unsigned value for bitvector with given width.
bvMaxUnsigned :: WidthRepr w -> BV w
bvMaxUnsigned w = BV (widthMask w)

-- FIXME: Should we pack the minimum signed and maximum signed values
-- into the 'WidthRepr'?
-- | The minimum value for bitvector in two's complement with given width.
bvMinSigned :: WidthRepr w -> BV w
bvMinSigned w = BV (bit (widthInt w - 1))

-- | The maximum value for bitvector in two's complement with given width.
bvMaxSigned :: WidthRepr w -> BV w
bvMaxSigned w = BV (bit (widthInt w - 1) - 1)

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a positive Integer.
bvIntegerUnsigned :: BV w -> Integer
bvIntegerUnsigned (BV x) = x

-- FIXME: In this, and other functions, we are converting to 'Int' in
-- order to use the underlying 'shiftL' function. This could be
-- problematic if the width is really huge.
-- | Signed interpretation of a bit vector as an Integer.
bvIntegerSigned :: WidthRepr w -> BV w -> Integer
bvIntegerSigned w (BV x) =
  if testBit x (width - 1)
  then x - (1 `shiftL` width)
  else x
  where width = widthInt w

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

-- | Bitwise complement (flip every bit).
bvComplement :: WidthRepr w -> BV w -> BV w
bvComplement w (BV x) = mkBV w (complement x)

-- | Left shift by positive 'Int'.
bvShl :: WidthRepr w -> BV w -> Int -> BV w
bvShl w (BV x) shf = mkBV w (x `shiftL` shf)

-- | Right arithmetic shift by positive 'Int'.
bvAshr :: WidthRepr w -> BV w -> Int -> BV w
bvAshr w bv shf = mkBV w (bvIntegerSigned w bv `shiftR` shf)

-- | Right logical shift.
bvLshr :: BV w -> Int -> BV w
bvLshr (BV x) shf = 
  -- Shift right (logical by default since the value is positive). No
  -- need to truncate bits, since the result is guaranteed to occupy
  -- no more bits than the input.
  BV (x `shiftR` shf)

-- | Bitwise rotate left.
bvRotateL :: WidthRepr w -> BV w -> Int -> BV w
bvRotateL w bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` width
        leftChunk = bvShl w bv rot
        rightChunk = bvLshr bv (width - rot)
        width = widthInt w

-- | Bitwise rotate right.
bvRotateR :: WidthRepr w -> BV w -> Int -> BV w
bvRotateR w bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` width
        rightChunk = bvLshr bv rot
        leftChunk = bvShl w bv (width - rot)
        width = widthInt w

-- | Test if a particular bit is set.
bvTestBit :: BV w -> Int -> Bool
bvTestBit (BV x) b = testBit x b

-- | Get the number of 1 bits in a 'BV'.
bvPopCount :: BV w -> Int
bvPopCount (BV x) = popCount x

-- | Truncate a bit vector to a particular width given at runtime,
-- while keeping the type-level width constant.
bvTruncBits :: BV w -> Int -> BV w
bvTruncBits (BV x) b = BV (x .&. (bit b - 1))

----------------------------------------
-- BV w arithmetic operations (fixed width)

-- | Bitwise add.
bvAdd :: WidthRepr w -> BV w -> BV w -> BV w
bvAdd w (BV x) (BV y) = mkBV w (x+y)

-- | Bitwise subtract.
bvSub :: WidthRepr w -> BV w -> BV w -> BV w
bvSub w (BV x) (BV y) = mkBV w (x-y)

-- | Bitwise multiply.
bvMul :: WidthRepr w -> BV w -> BV w -> BV w
bvMul w (BV x) (BV y) = mkBV w (x*y)

-- | Bitwise division (unsigned). Rounds to zero.
bvUquot :: BV w -> BV w -> BV w
bvUquot (BV x) (BV y) = BV (x `quot` y)

-- | Bitwise division (signed). Rounds to zero.
bvSquot :: WidthRepr w -> BV w -> BV w -> BV w
bvSquot w bv1 bv2 = mkBV w (x `quot` y)
  where x = bvIntegerSigned w bv1
        y = bvIntegerSigned w bv2

-- | Bitwise division (signed). Rounds to negative infinity.
bvSdiv :: WidthRepr w -> BV w -> BV w -> BV w
bvSdiv w bv1 bv2 = mkBV w (x `div` y)
  where x = bvIntegerSigned w bv1
        y = bvIntegerSigned w bv2

-- | Bitwise remainder after division (unsigned), when rounded to
-- zero.
bvUrem :: BV w -> BV w -> BV w
bvUrem (BV x) (BV y) = BV (x `rem` y)

-- | Bitwise remainder after division (signed), when rounded to zero.
bvSrem :: WidthRepr w -> BV w -> BV w -> BV w
bvSrem w bv1 bv2 = mkBV w (x `rem` y)
  where x = bvIntegerSigned w bv1
        y = bvIntegerSigned w bv2

-- | Bitwise remainder after division (signed), when rounded to
-- negative infinity.
bvSmod :: WidthRepr w -> BV w -> BV w -> BV w
bvSmod w bv1 bv2 = mkBV w (x `mod` y)
  where x = bvIntegerSigned w bv1
        y = bvIntegerSigned w bv2

-- | Bitwise absolute value.
bvAbs :: WidthRepr w -> BV w -> BV w
bvAbs w bv = mkBV w (abs (bvIntegerSigned w bv))

-- | Bitwise negation.
bvNegate :: WidthRepr w -> BV w -> BV w
bvNegate w (BV x) = mkBV w (-x)

-- | Get the sign bit as a 'BV'.
bvSignBit :: WidthRepr w -> BV w -> BV w
bvSignBit w bv@(BV _) = bvLshr bv (widthInt w - 1) `bvAnd` BV 1

-- | Signed less than.
bvSlt :: WidthRepr w -> BV w -> BV w -> Bool
bvSlt w bv1 bv2 = bvIntegerSigned w bv1 < bvIntegerSigned w bv2

-- | Signed less than or equal.
bvSle :: WidthRepr w -> BV w -> BV w -> Bool
bvSle w bv1 bv2 = bv1 == bv2 || bvSlt w bv1 bv2

-- | Unsigned less than.
bvUlt :: BV w -> BV w -> Bool
bvUlt bv1 bv2 = bvIntegerUnsigned bv1 < bvIntegerUnsigned bv2

-- | Unsigned less than or equal.
bvUle :: BV w -> BV w -> Bool
bvUle bv1 bv2 = bv1 == bv2 || bvUlt bv1 bv2

-- | Unsigned minimum of two bitvectors.
bvUmin :: BV w -> BV w -> BV w
bvUmin (BV x) (BV y) = if x < y then BV x else BV y

-- | Unsigned maximum of two bitvectors.
bvUmax :: BV w -> BV w -> BV w
bvUmax (BV x) (BV y) = if x < y then BV y else BV x

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
bvConcat :: WidthRepr w -> BV v -> BV w -> BV (v+w)
bvConcat loW (BV hi) (BV lo) =
  BV ((hi `shiftL` widthInt loW) .|. lo)

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
bvExtract :: WidthRepr w'
          -> Int
          -> BV w
          -> BV w'
bvExtract w' pos bv = mkBV w' xShf
  where (BV xShf) = bvLshr bv pos

-- | Zero-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvZext :: WidthRepr w'
       -> BV w
       -> BV w'
bvZext w' (BV x) = mkBV w' x

-- | Sign-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
bvSext :: WidthRepr w
       -> WidthRepr w'
       -> BV w
       -> BV w'
bvSext w w' bv = mkBV w' (bvIntegerSigned w bv)

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
