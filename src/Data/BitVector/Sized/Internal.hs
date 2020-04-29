{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.Internal
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

Internal hidden module containing all definitions for the 'BV' type.
-}

module Data.BitVector.Sized.Internal where

import Data.BitVector.Sized.Panic (panic)

import qualified Data.Bits as B
import qualified Numeric as N

import Data.Char (intToDigit)
import Data.Word
import Data.Parameterized ( NatRepr
                          , natValue
                          , intValue
                          , widthVal
                          , ShowF
                          , EqF(..)
                          , Hashable(..)
                          , HashableF(..))
import qualified Data.Parameterized.NatRepr as P
import GHC.Generics
import GHC.TypeLits
import Numeric.Natural
import Prelude hiding (abs, or, and, negate)
import qualified Prelude as Prelude

----------------------------------------
-- Utility functions

-- | Check that a 'NatRepr' is representable as an 'Int'.
checkNatRepr :: NatRepr w -> a -> a
checkNatRepr = checkNatural . natValue

-- | Check that a 'Natural' is representable as an 'Int'.
checkNatural :: Natural -> a -> a
checkNatural n a = if n > fromIntegral (maxBound :: Int)
  then panic "Data.BitVector.Sized.Internal.checkNatural"
       [show n <> " not representable as Int"]
  else a

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
-- BV construction
-- | Internal function for masking the input integer *without*
-- checking that the width is representable as an 'Int'. We use this
-- instead of 'mkBV' whenever we already have some guarantee that the
-- width is legal.
mkBV' :: NatRepr w -> Integer -> BV w
mkBV' w x = BV (P.toUnsigned w x)

-- | Construct a bitvector with a particular width, where the width is
-- provided as an explicit `NatRepr` argument. The input 'Integer',
-- whether positive or negative, is silently truncated to fit into the
-- number of bits demanded by the return type. The width cannot be
-- arbitrarily large; it must be representable as an 'Int'.
--
-- >>> mkBV (knownNat @4) 10
-- BV 10
-- >>> mkBV (knownNat @2) 10
-- BV 2
-- >>> mkBV (knownNat @4) (-2)
-- BV 14
mkBV :: NatRepr w
     -- ^ Desired width of bitvector
     -> Integer
     -- ^ Integer value to truncate to bitvector width
     -> BV w
mkBV w x = checkNatRepr w $ mkBV' w x

-- | Panic if an unsigned 'Integer' does not fit in the required
-- number of bits, otherwise return input.
checkUnsigned :: NatRepr w
              -> Integer
              -> Integer
checkUnsigned w i = if i < 0 || i > P.maxUnsigned w
  then panic "Data.BitVector.Sized.Internal.checkUnsigned"
       ["input out of bounds"]
  else i

-- | Like 'mkBV', but panics if unsigned input integer cannot be
-- represented in @w@ bits.
mkBVUnsafeUnsigned :: NatRepr w
                 -- ^ Desired width of bitvector
                 -> Integer
                 -- ^ Integer value
                 -> BV w
mkBVUnsafeUnsigned w x = checkNatRepr w $ BV (checkUnsigned w x)

-- | Panic if a signed 'Integer' does not fit in the required number
-- of bits. Returns an unsigned positive integer that fits in @w@
-- bits.
signedToUnsigned :: 1 <= w => NatRepr w
                 -- ^ Width of output
                 -> Integer
                 -> Integer
signedToUnsigned w i = if i < P.minSigned w || i > P.maxSigned w
  then panic "Data.BitVector.Sized.Internal.checkIntegerSigned"
       ["input out of bounds"]
  else if i < 0 then i + P.maxUnsigned w + 1 else i

-- | Like 'mkBV', but panics if signed input integer cannot be
-- represented in @w@ bits.
mkBVUnsafeSigned :: 1 <= w => NatRepr w
                 -- ^ Desired width of bitvector
                 -> Integer
                 -- ^ Integer value
                 -> BV w
mkBVUnsafeSigned w x = checkNatRepr w $ BV (signedToUnsigned w x)

-- | Construct a 'BV' from a 'Word8'.
word8 :: Word8 -> BV 8
word8 = BV . fromIntegral

-- | Construct a 'BV' from a 'Word16'.
word16 :: Word16 -> BV 16
word16 = BV . fromIntegral

-- | Construct a 'BV' from a 'Word32'.
word32 :: Word32 -> BV 32
word32 = BV . fromIntegral

-- | Construct a 'BV' from a 'Word64'.
word64 :: Word64 -> BV 64
word64 = BV . fromIntegral

-- | The minimum unsigned value for bitvector with given width (always 0).
minUnsigned :: NatRepr w -> BV w
minUnsigned w = checkNatRepr w $ BV 0

-- | The maximum unsigned value for bitvector with given width.
maxUnsigned :: NatRepr w -> BV w
maxUnsigned w = checkNatRepr w $ BV (P.maxUnsigned w)

-- | The minimum value for bitvector in two's complement with given width.
minSigned :: 1 <= w => NatRepr w -> BV w
minSigned w = mkBV w (P.minSigned w)

-- | The maximum value for bitvector in two's complement with given width.
maxSigned :: 1 <= w => NatRepr w -> BV w
maxSigned w = checkNatRepr w $ BV (P.maxSigned w)

-- | @unsignedClamp w i@ rounds @i@ to the nearest value between @0@
-- and @2^w - 1@ (inclusive).
unsignedClamp :: NatRepr w -> Integer -> BV w
unsignedClamp w x = checkNatRepr w $
  if | x < P.minUnsigned w -> BV (P.minUnsigned w)
     | x > P.maxUnsigned w -> BV (P.maxUnsigned w)
     | otherwise -> BV x

-- | @signedClamp w i@ rounds @i@ to the nearest value between
-- @-2^(w-1)@ and @2^(w-1) - 1@ (inclusive).
signedClamp :: 1 <= w => NatRepr w -> Integer -> BV w
signedClamp w x = checkNatRepr w $
  if | x < P.minSigned w -> BV (P.minSigned w)
     | x > P.maxSigned w -> BV (P.maxSigned w)
     | otherwise -> BV x

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bitvector as a positive Integer.
asUnsigned :: BV w -> Integer
asUnsigned (BV x) = x

-- | Signed interpretation of a bitvector as an Integer. Panic if
-- width is not representable as an 'Int'.
asSigned :: NatRepr w -> BV w -> Integer
asSigned w (BV x) =
  if B.testBit x (wInt - 1)
  then x - (1 `B.shiftL` wInt)
  else x
  where wInt = widthVal w

-- | Unsigned interpretation of a bitvector as a Natural.
asNatural :: BV w -> Natural
asNatural = fromIntegral . asUnsigned

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
complement w (BV x) = mkBV' w (B.complement x)

-- | Left shift by positive 'Natural'.
shl :: NatRepr w -> BV w -> Natural -> BV w
shl w (BV x) shf = checkNatural shf $
  mkBV' w (x `B.shiftL` fromIntegral shf)

-- | Right arithmetic shift by positive 'Natural'.
ashr :: NatRepr w -> BV w -> Natural -> BV w
ashr w bv shf = checkNatural shf $
  mkBV' w (asSigned w bv `B.shiftR` fromIntegral shf)

-- | Right logical shift by positive 'Natural'.
lshr :: BV w -> Natural -> BV w
lshr (BV x) shf = checkNatural shf $
  -- Shift right (logical by default since the value is positive). No
  -- need to truncate bits, since the result is guaranteed to occupy
  -- no more bits than the input.
  BV (x `B.shiftR` fromIntegral shf)

-- | Bitwise rotate left.
rotateL :: NatRepr w -> BV w -> Natural -> BV w
rotateL w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` wNatural
        leftChunk = shl w bv rot
        rightChunk = lshr bv (wNatural - rot)
        wNatural = natValue w

-- | Bitwise rotate right.
rotateR :: NatRepr w -> BV w -> Natural -> BV w
rotateR w bv rot' = leftChunk `or` rightChunk
  where rot = rot' `mod` wNatural
        rightChunk = lshr bv rot
        leftChunk = shl w bv (wNatural - rot)
        wNatural = natValue w

-- | The zero bitvector of any width.
zero :: NatRepr w -> BV w
zero w = checkNatRepr w $ BV 0

-- | The bitvector with value 1, of any positive width.
one :: 1 <= w => NatRepr w -> BV w
one w = checkNatRepr w $ BV 1

-- | The bitvector whose value is its own width, of any width.
width :: NatRepr w -> BV w
width w = checkNatRepr w $ BV (intValue w)

-- | The 'BV' that has a particular bit set, and is 0 everywhere
-- else.
bit :: ix+1 <= w
    => NatRepr w
    -- ^ Desired output width
    -> NatRepr ix
    -- ^ Index of bit to set
    -> BV w
bit w ix = checkNatRepr w $ BV (B.bit (widthVal ix))

-- | Like 'bit', but without the requirement that the index bit refers
-- to an actual bit in the output 'BV'. If it is out of range, just
-- silently return the zero bitvector.
bit' :: NatRepr w
     -- ^ Desired output width
     -> Natural
     -- ^ Index of bit to set
     -> BV w
bit' w ix = mkBV w (B.bit (fromIntegral ix))

-- | @setBit w bv ix@ is the same as @or bv (bit w ix)@.
setBit :: ix+1 <= w
       => NatRepr w
       -- ^ Desired output width
       -> NatRepr ix
       -- ^ Index of bit to set
       -> BV w
       -- ^ Original bitvector
       -> BV w
setBit w ix bv = or bv (bit w ix)

-- | Like 'setBit', but without the requirement that the index bit
-- refers to an actual bit in the input 'BV'. If it is out of range,
-- just silently return the original input.
setBit' :: NatRepr w
        -- ^ Desired output width
        -> Natural
        -- ^ Index of bit to set
        -> BV w
        -- ^ Original bitvector
        -> BV w
setBit' w ix bv = or bv (bit' w ix)

-- | @clearBit w bv ix@ is the same as @and bv (complement (bit w ix))@.
clearBit :: ix+1 <= w
         => NatRepr w
         -- ^ Desired output width
         -> NatRepr ix
         -- ^ Index of bit to clear
         -> BV w
         -- ^ Original bitvector
         -> BV w
clearBit w ix bv = and bv (complement w (bit w ix))

-- | Like 'clearBit', but without the requirement that the index bit
-- refers to an actual bit in the input 'BV'. If it is out of range,
-- just silently return the original input.
clearBit' :: NatRepr w
          -- ^ Desired output width
          -> Natural
          -- ^ Index of bit to clear
          -> BV w
          -- ^ Original bitvector
          -> BV w
clearBit' w ix bv = and bv (complement w (bit' w ix))

-- | @complementBit w bv ix@ is the same as @xor bv (bit w ix)@.
complementBit :: ix+1 <= w
              => NatRepr w
              -- ^ Desired output width
              -> NatRepr ix
              -- ^ Index of bit to flip
              -> BV w
              -- ^ Original bitvector
              -> BV w
complementBit w ix bv = xor bv (bit w ix)

-- | Like 'complementBit', but without the requirement that the index
-- bit refers to an actual bit in the input 'BV'. If it is out of
-- range, just silently return the original input. Panic if index is
-- not representable as an 'Int'.
complementBit' :: NatRepr w
               -- ^ Desired output width
               -> Natural
               -- ^ Index of bit to flip
               -> BV w
               -- ^ Original bitvector
               -> BV w
complementBit' w ix bv = xor bv (bit' w ix)

-- | Test if a particular bit is set. Panic if index is not
-- representable as an 'Int'.
testBit :: ix+1 <= w => NatRepr ix -> BV w -> Bool
testBit ix (BV x) = B.testBit x (widthVal ix)

-- | Like 'testBit', but takes a 'Natural' for the bit index. If the
-- index is out of bounds, return 'False'. Panic if input is not
-- representable as an 'Int'.
testBit' :: Natural -> BV w -> Bool
testBit' ix (BV x) = B.testBit x (fromIntegral ix)

-- | Get the number of 1 bits in a 'BV'.
popCount :: BV w -> BV w
popCount (BV x) = BV (fromIntegral (B.popCount x))

-- | Count trailing zeros in a 'BV'.
ctz :: NatRepr w -> BV w -> BV w
ctz w (BV x) = BV (go 0)
  where go !i | i < toInteger (natValue w) &&
                B.testBit x (fromInteger i) == False = go (i+1)
              | otherwise = i

-- | Count leading zeros in a 'BV'.
clz :: NatRepr w -> BV w -> BV w
clz w (BV x) = BV (go 0)
 where go !i | i < toInteger (natValue w) &&
               B.testBit x (widthVal w - fromInteger i - 1) == False =
                 go (i+1)
             | otherwise = i

-- | Truncate a bitvector to a particular width given at runtime,
-- while keeping the type-level width constant.
truncBits :: Natural -> BV w -> BV w
truncBits b (BV x) = BV (x B..&. (B.bit (fromIntegral b) - 1))

----------------------------------------
-- BV w arithmetic operations (fixed width)

-- | Bitvector add.
add :: NatRepr w -> BV w -> BV w -> BV w
add w (BV x) (BV y) = mkBV w (x+y)

-- | Bitvector subtract.
sub :: NatRepr w -> BV w -> BV w -> BV w
sub w (BV x) (BV y) = mkBV w (x-y)

-- | Bitvector multiply.
mul :: NatRepr w -> BV w -> BV w -> BV w
mul w (BV x) (BV y) = mkBV w (x*y)

-- | Bitvector division (unsigned). Rounds to zero. Division by zero
-- yields a runtime error.
uquot :: BV w -> BV w -> BV w
uquot (BV x) (BV y) = BV (x `quot` y)

-- | Bitvector division (signed). Rounds to zero. Division by zero
-- yields a runtime error.
squot :: NatRepr w -> BV w -> BV w -> BV w
squot w bv1 bv2 = mkBV w (x `quot` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitvector division (signed). Rounds to negative infinity. Division
-- by zero yields a runtime error.
sdiv :: NatRepr w -> BV w -> BV w -> BV w
sdiv w bv1 bv2 = mkBV w (x `div` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitvector remainder after division (unsigned), when rounded to
-- zero. Division by zero yields a runtime error.
urem :: BV w -> BV w -> BV w
urem (BV x) (BV y) = BV (x `rem` y)

-- | Bitvector remainder after division (signed), when rounded to
-- zero. Division by zero yields a runtime error.
srem :: NatRepr w -> BV w -> BV w -> BV w
srem w bv1 bv2 = mkBV w (x `rem` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitvector remainder after division (signed), when rounded to
-- negative infinity. Division by zero yields a runtime error.
smod :: NatRepr w -> BV w -> BV w -> BV w
smod w bv1 bv2 = mkBV w (x `mod` y)
  where x = asSigned w bv1
        y = asSigned w bv2

-- | Bitvector absolute value.
abs :: NatRepr w -> BV w -> BV w
abs w bv = mkBV w (Prelude.abs (asSigned w bv))

-- | Bitvector negation.
negate :: NatRepr w -> BV w -> BV w
negate w (BV x) = mkBV w (-x)

-- | Get the sign bit as a 'BV'.
signBit :: 1 <= w => NatRepr w -> BV w -> BV w
signBit w bv@(BV _) = lshr bv (natValue w - 1) `and` BV 1

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

-- | Signed minimum of two bitvectors.
smin :: NatRepr w -> BV w -> BV w -> BV w
smin w bv1 bv2 = if asSigned w bv1 < asSigned w bv2 then bv1 else bv2

-- | Signed minimum of two bitvectors.
smax :: NatRepr w -> BV w -> BV w -> BV w
smax w bv1 bv2 = if asSigned w bv1 < asSigned w bv2 then bv2 else bv1

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
  BV ((hi `B.shiftL` (widthVal loW)) B..|. lo)

-- | Slice out a smaller bitvector from a larger one.
--
-- >>> select (knownNat @4) (knownNat @1) (mkBV (knownNat @12) 0b110010100110)
-- BV 3
-- >>> :type it
-- it :: BV 4
select :: ix + w' <= w
       => NatRepr ix
       -- ^ Index to start selecting from
       -> NatRepr w'
       -- ^ Desired output width
       -> BV w
       -- ^ Bitvector to select from
       -> BV w'
select ix w' bv = mkBV w' xShf
  where (BV xShf) = lshr bv (natValue ix)

-- | Like 'select', but takes a 'Natural' as the index to start
-- selecting from. Neither the index nor the output width is checked
-- to ensure the resulting 'BV' lies entirely within the bounds of the
-- original bitvector. Any bits "selected" from beyond the bounds of
-- the input bitvector will be 0.
--
-- >>> select' (knownNat @4) 9 (mkBV (knownNat @12) 0b110010100110)
-- BV 6
-- >>> :type it
-- it :: BV 4
select' :: Natural
        -- ^ Index to start selecting from
        -> NatRepr w'
        -- ^ Desired output width
        -> BV w
        -- ^ Bitvector to select from
        -> BV w'
select' ix w' bv = mkBV w' xShf
  where (BV xShf) = lshr bv ix

-- | Zero-extend a bitvector to one of strictly greater width.
--
-- >>> zext (knownNat @8) (mkBV (knownNat @4) 0b1101)
-- BV 13
-- >>> :type it
-- it :: BV 8
zext :: w + 1 <= w'
     => NatRepr w'
     -- ^ Desired output width
     -> BV w
     -- ^ Bitvector to extend
     -> BV w'
zext _ (BV x) = BV x

-- | Sign-extend a bitvector to one of strictly greater width.
sext :: w + 1 <= w'
     => NatRepr w
     -- ^ Width of input bitvector
     -> NatRepr w'
     -- ^ Desired output width
     -> BV w
     -- ^ Bitvector to extend
     -> BV w'
sext w w' bv = mkBV w' (asSigned w bv)

-- | Truncate a bitvector to one of strictly smaller width.
trunc :: w' + 1 <= w
      => NatRepr w'
      -- ^ Desired output width
      -> BV w
      -- ^ Bitvector to truncate
      -> BV w'
trunc w' (BV x) = mkBV w' x

-- | Like 'trunc', but allows the input width to be greater than or
-- equal to the output width, in which case it just performs a zero
-- extension.
trunc' :: NatRepr w'
      -- ^ Desired output width
      -> BV w
      -- ^ Bitvector to truncate
      -> BV w'
trunc' w' (BV x) = mkBV w' x

-- | Wide multiply of two bitvectors.
mulWide :: BV w -> BV v -> BV (w+v)
mulWide (BV x) (BV y) = BV (x*y)

----------------------------------------
-- Enum functions

-- | Unsigned successor. @succUnsigned w (maxUnsigned w)@ returns 'Nothing'.
succUnsigned :: NatRepr w -> BV w -> Maybe (BV w)
succUnsigned w (BV x) =
  if x == P.maxUnsigned w
  then Nothing
  else Just (BV (x+1))

-- | Signed successor. @succSigned w (maxSigned w)@ returns 'Nothing'.
succSigned :: 1 <= w => NatRepr w -> BV w -> Maybe (BV w)
succSigned w (BV x) =
  if x == P.maxSigned w
  then Nothing
  else Just (mkBV w (x+1))

-- | Unsigned predecessor. @predUnsigned w zero@ returns 'Nothing'.
predUnsigned :: NatRepr w -> BV w -> Maybe (BV w)
predUnsigned w (BV x) =
  if x == P.minUnsigned w
  then Nothing
  else Just (BV (x-1))

-- | Signed predecessor. @predSigned w (minSigned w)@ returns 'Nothing'.
predSigned :: 1 <= w => NatRepr w -> BV w -> Maybe (BV w)
predSigned w bv@(BV x) =
  if bv == minSigned w
  then Nothing
  else Just (mkBV w (x-1))

-- | List of all unsigned bitvectors from a lower to an upper bound,
-- inclusive.
enumFromToUnsigned :: BV w
                   -- ^ Lower bound
                   -> BV w
                   -- ^ Upper bound
                   -> [BV w]
enumFromToUnsigned bv1 bv2 = BV <$> [asUnsigned bv1 .. asUnsigned bv2]

-- | List of all signed bitvectors from a lower to an upper bound,
-- inclusive.
enumFromToSigned :: 1 <= w => NatRepr w
                 -> BV w
                 -- ^ Lower bound
                 -> BV w
                 -- ^ Upper bound
                 -> [BV w]
enumFromToSigned w bv1 bv2 = BV <$> signedToUnsigned w <$> [asSigned w bv1 .. asSigned w bv2]

----------------------------------------
-- Pretty printing

-- | Pretty print in hex
ppHex :: NatRepr w -> BV w -> String
ppHex w (BV x) = "0x" ++ N.showHex x "" ++ ":" ++ ppWidth w

-- | Pretty print in binary
ppBin :: NatRepr w -> BV w -> String
ppBin w (BV x) = "0b" ++ N.showIntAtBase 2 intToDigit x "" ++ ":" ++ ppWidth w

-- | Pretty print in octal
ppOct :: NatRepr w -> BV w -> String
ppOct w (BV x) = "0o" ++ N.showOct x "" ++ ":" ++ ppWidth w

-- | Pretty print in decimal
ppDec :: NatRepr w -> BV w -> String
ppDec w (BV x) = show x ++ ":" ++ ppWidth w

ppWidth :: NatRepr w -> String
ppWidth w = "[" ++ show (natValue w) ++ "]"
