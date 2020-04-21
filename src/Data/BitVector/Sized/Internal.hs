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

import qualified Data.Bits as B
import qualified Data.Parameterized as P
import qualified Prelude as Prelude

import Data.Parameterized (NatRepr)
import GHC.Generics
import GHC.TypeLits
import Prelude hiding (abs, or, and)

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

instance P.ShowF BV

instance P.EqF BV where
  BV bv `eqF` BV bv' = bv == bv'

instance P.Hashable (BV w) where
  hashWithSalt salt (BV i) = P.hashWithSalt salt i

instance P.HashableF BV where
  hashWithSaltF salt (BV i) = P.hashWithSalt salt i

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
mkBV :: NatRepr w -> Integer -> BV w
mkBV w x = BV (P.toUnsigned w x)

-- | The zero bitvector of any width.
zero :: BV w
zero = BV 0

-- | The 'BitVector' that has a particular bit set, and is 0
-- everywhere else.
bit :: (0 <= w', w' <= w) => NatRepr w' -> BV w
bit ix = BV (B.bit (P.widthVal ix))

-- | Like 'bvBit', but without the requirement that the index bit
-- refers to an actual bit in the input 'BV'. If it is out of range,
-- just silently return 0.
bit' :: NatRepr w -> Int -> BV w
bit' w ix = mkBV w (B.bit ix)

-- | The minimum unsigned value for bitvector with given width (always 0).
minUnsigned :: BV w
minUnsigned = BV 0

-- | The maximum unsigned value for bitvector with given width.
maxUnsigned :: NatRepr w -> BV w
maxUnsigned w = BV (P.maxUnsigned w)

-- | The minimum value for bitvector in two's complement with given width.
minSigned :: 1 <= w => NatRepr w -> BV w
minSigned w = BV (P.minSigned w)

-- | The maximum value for bitvector in two's complement with given width.
maxSigned :: 1 <= w => NatRepr w -> BV w
maxSigned w = BV (P.maxSigned w)

unsignedClamp :: NatRepr w -> Integer -> BV w
unsignedClamp w x = BV (P.unsignedClamp w x)

signedClamp :: 1 <= w => NatRepr w -> Integer -> BV w
signedClamp w x = BV (P.signedClamp w x)

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a positive Integer.
asUnsigned :: BV w -> Integer
asUnsigned (BV x) = x

-- FIXME: In this, and other functions, we are converting to 'Int' in
-- order to use the underlying 'shiftL' function. This could be
-- problematic if the width is really huge.
-- | Signed interpretation of a bit vector as an Integer.
asSigned :: NatRepr w -> BV w -> Integer
asSigned w (BV x) =
  if B.testBit x (width - 1)
  then x - (1 `B.shiftL` width)
  else x
  where width = P.widthVal w

----------------------------------------
-- BV w operations (fixed width)

-- | Bitwise and.
and :: BV w -> BV w -> BV w
and (BV x) (BV y) = BV (x B..&. y)

-- | Bitwise or.
or :: BV w -> BV w -> BV w
or (BV x) (BV y) = BV (x B..|. y)

-- | Bitwise xor.
xor :: BV w -> BV w -> BV w
xor (BV x) (BV y) = BV (x `B.xor` y)

-- | Bitwise complement (flip every bit).
complement :: NatRepr w -> BV w -> BV w
complement w (BV x) = mkBV w (B.complement x)

-- | Left shift by positive 'Int'.
shl :: NatRepr w -> BV w -> Int -> BV w
shl w (BV x) shf = mkBV w (x `B.shiftL` shf)

-- | Right arithmetic shift by positive 'Int'.
ashr :: NatRepr w -> BV w -> Int -> BV w
ashr w bv shf = mkBV w (asSigned w bv `B.shiftR` shf)

-- | Right logical shift.
lshr :: BV w -> Int -> BV w
lshr (BV x) shf = 
  -- Shift right (logical by default since the value is positive). No
  -- need to truncate bits, since the result is guaranteed to occupy
  -- no more bits than the input.
  BV (x `B.shiftR` shf)

-- | Bitwise rotate left.
rotateL :: NatRepr w -> BV w -> Int -> BV w
rotateL w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` width
        leftChunk = shl w bv rot
        rightChunk = lshr bv (width - rot)
        width = P.widthVal w

-- | Bitwise rotate right.
rotateR :: NatRepr w -> BV w -> Int -> BV w
rotateR w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` width
        rightChunk = lshr bv rot
        leftChunk = shl w bv (width - rot)
        width = P.widthVal w

-- | Test if a particular bit is set.
testBit :: BV w -> Int -> Bool
testBit (BV x) b = B.testBit x b

-- | Get the number of 1 bits in a 'BV'.
popCount :: BV w -> Int
popCount (BV x) = B.popCount x

-- | Truncate a bit vector to a particular width given at runtime,
-- while keeping the type-level width constant.
truncBits :: BV w -> Int -> BV w
truncBits (BV x) b = BV (x B..&. (B.bit b - 1))

----------------------------------------
-- BV w arithmetic operations (fixed width)

-- | Bitwise add.
add :: NatRepr w -> BV w -> BV w -> BV w
add w (BV x) (BV y) = mkBV w (x+y)

-- | Bitwise subtract.
sub :: NatRepr w -> BV w -> BV w -> BV w
sub w (BV x) (BV y) = mkBV w (x-y)

-- | Bitwise multiply.
mul :: NatRepr w -> BV w -> BV w -> BV w
mul w (BV x) (BV y) = mkBV w (x*y)

-- | Bitwise division (unsigned). Rounds to zero.
uquot :: BV w -> BV w -> BV w
uquot (BV x) (BV y) = BV (x `quot` y)

-- | Bitwise division (signed). Rounds to zero.
squot :: NatRepr w -> BV w -> BV w -> BV w
squot w bv1 bv2 = mkBV w (x `quot` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitwise division (signed). Rounds to negative infinity.
sdiv :: NatRepr w -> BV w -> BV w -> BV w
sdiv w bv1 bv2 = mkBV w (x `div` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitwise remainder after division (unsigned), when rounded to
-- zero.
urem :: BV w -> BV w -> BV w
urem (BV x) (BV y) = BV (x `rem` y)

-- | Bitwise remainder after division (signed), when rounded to zero.
srem :: NatRepr w -> BV w -> BV w -> BV w
srem w bv1 bv2 = mkBV w (x `rem` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitwise remainder after division (signed), when rounded to
-- negative infinity.
smod :: NatRepr w -> BV w -> BV w -> BV w
smod w bv1 bv2 = mkBV w (x `mod` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitwise absolute value.
abs :: NatRepr w -> BV w -> BV w
abs w bv = mkBV w (Prelude.abs (asSigned w bv))

-- | Bitwise negation.
negate :: NatRepr w -> BV w -> BV w
negate w (BV x) = mkBV w (-x)

-- | Get the sign bit as a 'BV'.
signBit :: NatRepr w -> BV w -> BV w
signBit w bv@(BV _) = lshr bv (P.widthVal w - 1) `and` BV 1

-- | Signed less than.
slt :: NatRepr w -> BV w -> BV w -> Bool
slt w bv1 bv2 = asSigned w bv1 < asSigned w bv2

-- | Signed less than or equal.
sle :: NatRepr w -> BV w -> BV w -> Bool
sle w bv1 bv2 = bv1 == bv2 || slt w bv1 bv2

-- | Unsigned less than.
ult :: BV w -> BV w -> Bool
ult bv1 bv2 = asUnsigned bv1 < asUnsigned bv2

-- | Unsigned less than or equal.
ule :: BV w -> BV w -> Bool
ule bv1 bv2 = bv1 == bv2 || ult bv1 bv2

-- | Unsigned minimum of two bitvectors.
umin :: BV w -> BV w -> BV w
umin (BV x) (BV y) = if x < y then BV x else BV y

-- | Unsigned maximum of two bitvectors.
umax :: BV w -> BV w -> BV w
umax (BV x) (BV y) = if x < y then BV y else BV x

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
concat :: NatRepr w -> BV v -> BV w -> BV (v+w)
concat loW (BV hi) (BV lo) =
  BV ((hi `B.shiftL` P.widthVal loW) B..|. lo)

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
extract :: NatRepr w'
        -> Int
        -> BV w
        -> BV w'
extract w' pos bv = mkBV w' xShf
  where (BV xShf) = lshr bv pos

-- | Zero-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
zext :: NatRepr w'
     -> BV w
     -> BV w'
zext w' (BV x) = mkBV w' x

-- | Sign-extend a vector to one of greater length. If given an input of greater
-- length than the output type, this performs a truncation.
sext :: NatRepr w
     -> NatRepr w'
     -> BV w
     -> BV w'
sext w w' bv = mkBV w' (asSigned w bv)
