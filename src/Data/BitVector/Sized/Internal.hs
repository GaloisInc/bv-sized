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
import Numeric.Natural
import Prelude hiding (abs, or, and)

-- | Convert an 'Integer' to an 'Int', and panic if the input takes up
-- too many bits.
toInt :: Natural -> Int
toInt i = if i > fromIntegral (maxBound :: Int)
          then error "PANIC: toInt called with large Natural"
          else fromIntegral i

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
-- BV construction
-- | Construct a bitvector with a particular width, where the width is
-- provided as an explicit `NatRepr` argument. The input (an unbounded
-- data type, hence with an infinite-width bit representation),
-- whether positive or negative, is silently truncated to fit into the
-- number of bits demanded by the return type.
--
-- >>> mkBV (knownNat @4) 10
-- BV 10
-- >>> mkBV (knownNat @2) 10
-- BV 2
mkBV :: NatRepr w -> Integer -> BV w
mkBV w x = BV (P.toUnsigned w x)

-- | The zero bitvector of any width.
zero :: BV w
zero = BV 0

-- | The 'BV' that has a particular bit set, and is 0 everywhere else.
bit :: (0 <= w', w'+1 <= w) => NatRepr w' -> BV w
bit ix = BV (B.bit (toInt (P.natValue ix)))

-- | Like 'bit', but without the requirement that the index bit refers
-- to an actual bit in the input 'BV'. If it is out of range, just
-- silently return 0.
bit' :: NatRepr w -> Natural -> BV w
bit' w ix = mkBV w (B.bit (toInt ix))

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

-- | @unsignedClamp w i@ rounds @i@ to the nearest value between @0@
-- and @2^w - 1@ (inclusive).
unsignedClamp :: NatRepr w -> Integer -> BV w
unsignedClamp w x = BV (P.unsignedClamp w x)

-- | @signedClamp w i@ rounds @i@ to the nearest value between
-- @-2^(w-1)@ and @2^(w-1) - 1@ (inclusive).
signedClamp :: 1 <= w => NatRepr w -> Integer -> BV w
signedClamp w x = BV (P.signedClamp w x)

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bitvector as a positive Integer.
asUnsigned :: BV w -> Integer
asUnsigned (BV x) = x

-- FIXME: In this, and other functions, we are converting to 'Int' in
-- order to use the underlying 'shiftL' function. This could be
-- problematic if the width is really huge.
-- | Signed interpretation of a bitvector as an Integer.
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

-- | Left shift by positive 'Natural'.
shl :: NatRepr w -> BV w -> Natural -> BV w
shl w (BV x) shf = mkBV w (x `B.shiftL` toInt shf)

-- | Right arithmetic shift by positive 'Natural'.
ashr :: NatRepr w -> BV w -> Natural -> BV w
ashr w bv shf = mkBV w (asSigned w bv `B.shiftR` toInt shf)

-- | Right logical shift.
lshr :: BV w -> Natural -> BV w
lshr (BV x) shf = 
  -- Shift right (logical by default since the value is positive). No
  -- need to truncate bits, since the result is guaranteed to occupy
  -- no more bits than the input.
  BV (x `B.shiftR` toInt shf)

-- | Bitwise rotate left.
rotateL :: NatRepr w -> BV w -> Natural -> BV w
rotateL w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` width
        leftChunk = shl w bv rot
        rightChunk = lshr bv (width - rot)
        width = P.natValue w

-- | Bitwise rotate right.
rotateR :: NatRepr w -> BV w -> Natural -> BV w
rotateR w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` width
        rightChunk = lshr bv rot
        leftChunk = shl w bv (width - rot)
        width = P.natValue w

-- | Test if a particular bit is set.
testBit :: BV w -> Natural -> Bool
testBit (BV x) b = B.testBit x (toInt b)

-- | Get the number of 1 bits in a 'BV'.
popCount :: BV w -> Integer
popCount (BV x) = toInteger (B.popCount x)

-- | Truncate a bitvector to a particular width given at runtime,
-- while keeping the type-level width constant.
truncBits :: BV w -> Natural -> BV w
truncBits (BV x) b = BV (x B..&. (B.bit (toInt b) - 1))

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
signBit :: 1 <= w => NatRepr w -> BV w -> BV w
signBit w bv@(BV _) = lshr bv (P.natValue w - 1) `and` BV 1

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

-- | Concatenate two bitvectors. The first argument gets placed in the
-- higher order bits.
--
-- >>> concat knownNat (mkBV (knownNat @3) 0b001) (mkBV (knownNat @2) 0b10)
-- BV 6
-- >>> :type it
-- it :: BV 5
concat :: NatRepr w
       -- ^ Width of lower-order bits (for shifting purposes)
       -> BV v
       -- ^ Higher-order bits
       -> BV w
       -- ^ Lower-order bits
       -> BV (v+w)
concat loW (BV hi) (BV lo) =
  BV ((hi `B.shiftL` P.widthVal loW) B..|. lo)

-- | Slice out a smaller bitvector from a larger one.
--
-- >>> extract (knownNat @4) (knownNat @1) (mkBV (knownNat @12) 0b110010100110)
-- BV 3
-- >>> :type it
-- it :: BV 4
extract :: ix + w' <= w
        => NatRepr w'
        -- ^ Desired output width
        -> NatRepr ix
        -- ^ Index to start extracting from
        -> BV w
        -- ^ Bitvector to extract from
        -> BV w'
extract w' ix bv = mkBV w' xShf
  where (BV xShf) = lshr bv (P.natValue ix)

-- | Like 'extract', but takes a 'Natural' as the index to start
-- extracting from. Neither the index nor the output width is checked
-- to ensure the resulting 'BV' lies entirely within the bounds of the
-- original bitvector. Any bits "extracted" from beyond the bounds of
-- the input bitvector will be 0.
--
-- >>> extract' (knownNat @4) 9 (mkBV (knownNat @12) 0b110010100110)
-- BV 6
-- >>> :type it
-- it :: BV 4
extract' :: NatRepr w'
         -- ^ Desired output width
         -> Natural
         -- ^ Index to start extracting from
         -> BV w
         -- ^ Bitvector to extract from
         -> BV w'
extract' w' pos bv = mkBV w' xShf
  where (BV xShf) = lshr bv pos

-- | Zero-extend a bitvector to one of greater width.
--
-- >>> zext (knownNat @8) (mkBV (knownNat @4) 0b1101)
-- BV 13
-- >>> :type it
-- it :: BV 8
zext :: w <= w'
     => NatRepr w'
     -- ^ Desired output width
     -> BV w
     -- ^ Bitvector to extend
     -> BV w'
zext _ (BV x) = BV x

-- | Sign-extend a bitvector to one of greater width.
sext :: w <= w'
     => NatRepr w
     -- ^ Width of input bitvector
     -> NatRepr w'
     -- ^ Desired output width
     -> BV w
     -- ^ Bitvector to extend
     -> BV w'
sext w w' bv = mkBV w' (asSigned w bv)

-- | Truncate a bitvector to one of smaller width.
trunc :: w' <= w
      => NatRepr w'
      -- ^ Desired output width
      -> BV w
      -- ^ Bitvector to truncate
      -> BV w'
trunc w' (BV x) = mkBV w' x

-- | Like 'trunc', but allows the input width to be greater than the
-- output width, in which case it just performs a zero extension.
trunc' :: NatRepr w'
      -- ^ Desired output width
      -> BV w
      -- ^ Bitvector to truncate
      -> BV w'
trunc' w' (BV x) = mkBV w' x
