{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Data.BitVector.Sized.Unsigned
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a wrapper around the 'BV' type, 'UnsignedBV', with
instances not provided by 'BV'.
-}

module Data.BitVector.Sized.Unsigned
  ( UnsignedBV(..)
    -- * Constructors
  , mkUnsignedBV, mkUnsignedBV'
  , clamp
  , zero, one, width
    -- * Construction from fixed-width data types
  , bool, word8, word16, word32, word64
  , bitsBE, bitsLE
  , bytestringBE, bytestringLE
  , bytesBE, bytesLE
    -- * Conversions to primitive types
  , asBitsBE, asBitsLE
  , asBytesBE, asBytesLE
  , asBytestringBE, asBytestringLE
    -- * Bitwise operations
    -- | Useful functions not in @Data.Bits@.
  , ctz, clz
  , truncBits
  , signBit
    -- * Width-changing operations
  , concat
  , select
  , select'
  , ext
  , trunc
  , resize
  , mulWide
    -- * Pretty printing
  , ppHex
  , ppBin
  , ppOct
  , ppDec
  ) where

import           Data.BitVector.Sized.Internal (BV(..), mkBV)
import qualified Data.BitVector.Sized.Internal as BV
import           Data.BitVector.Sized.Panic (panic)
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr (NatRepr, knownNat, maxUnsigned, widthVal)
import           Data.Parameterized.Pair

import Data.Bits (Bits(..), FiniteBits(..))
import qualified Data.ByteString as BS
import Data.Ix (Ix(inRange, range, index))
import Data.Word
import GHC.Generics (Generic)
import GHC.TypeLits (KnownNat, type (<=), type (+))
import Numeric.Natural (Natural)
import Prelude hiding (concat)
import System.Random
import System.Random.Stateful

-- | Signed bit vector.
newtype UnsignedBV w = UnsignedBV { asBV :: BV w }
  deriving (Generic, Show, Read, Eq, Ord)

instance ShowF UnsignedBV

-- | Convenience wrapper for 'BV.mkBV'.
mkUnsignedBV :: NatRepr w -> Integer -> UnsignedBV w
mkUnsignedBV w x = UnsignedBV (BV.mkBV w x)

-- | Convenience wrapper for 'BV.mkBVUnsigned'.
mkUnsignedBV' :: NatRepr w -> Integer -> Maybe (UnsignedBV w)
mkUnsignedBV' w x = UnsignedBV <$> BV.mkBVUnsigned w x

liftUnary :: (BV w -> BV w)
          -> UnsignedBV w
          -> UnsignedBV w
liftUnary op (UnsignedBV bv) = UnsignedBV (op bv)

liftBinary :: (BV w -> BV w -> BV w)
           -> UnsignedBV w
           -> UnsignedBV w
           -> UnsignedBV w
liftBinary op (UnsignedBV bv1) (UnsignedBV bv2) = UnsignedBV (op bv1 bv2)

liftBinaryInt :: (BV w -> Natural -> BV w)
              -> UnsignedBV w
              -> Int
              -> UnsignedBV w
liftBinaryInt op (UnsignedBV bv) i = UnsignedBV (op bv (intToNatural i))

intToNatural :: Int -> Natural
intToNatural = fromIntegral

instance KnownNat w => Bits (UnsignedBV w) where
  (.&.)        = liftBinary BV.and
  (.|.)        = liftBinary BV.or
  xor          = liftBinary BV.xor
  complement   = liftUnary (BV.complement knownNat)
  shiftL       = liftBinaryInt (BV.shl knownNat)
  shiftR       = liftBinaryInt (BV.lshr knownNat)
  rotateL      = liftBinaryInt (BV.rotateL knownNat)
  rotateR      = liftBinaryInt (BV.rotateR knownNat)
  bitSize _    = widthVal (knownNat @w)
  bitSizeMaybe _ = Just (widthVal (knownNat @w))
  isSigned     = const False
  testBit (UnsignedBV bv) ix = BV.testBit' (intToNatural ix) bv
  bit          = UnsignedBV . BV.bit' knownNat . intToNatural
  popCount (UnsignedBV bv) = fromInteger (BV.asUnsigned (BV.popCount bv))

instance KnownNat w => FiniteBits (UnsignedBV w) where
  finiteBitSize _ = widthVal (knownNat @w)
  countLeadingZeros  (UnsignedBV bv) = fromInteger $ BV.asUnsigned $ BV.clz knownNat bv
  countTrailingZeros (UnsignedBV bv) = fromInteger $ BV.asUnsigned $ BV.ctz knownNat bv

instance KnownNat w => Num (UnsignedBV w) where
  (+)         = liftBinary (BV.add knownNat)
  (*)         = liftBinary (BV.mul knownNat)
  abs         = id
  signum (UnsignedBV bv) = UnsignedBV $ BV.BV $ signum $ BV.asUnsigned bv
  fromInteger = UnsignedBV . mkBV knownNat
  -- in this case, negate just means "additive inverse"
  negate      = liftUnary (BV.negate knownNat)

instance KnownNat w => Real (UnsignedBV w) where
  toRational (UnsignedBV (BV x)) = fromInteger x

instance KnownNat w => Integral (UnsignedBV w) where
  toInteger (UnsignedBV (BV x)) = x
  UnsignedBV bv `quotRem` UnsignedBV bv' =
    let (q, r) = bv `BV.uquotRem` bv'
    in (UnsignedBV q, UnsignedBV r)

instance KnownNat w => Enum (UnsignedBV w) where
  toEnum = UnsignedBV . mkBV knownNat . checkInt
    where checkInt i | 0 <= i && toInteger i <= (maxUnsigned (knownNat @w)) = toInteger i
                     | otherwise = panic "Data.BitVector.Sized.Unsigned"
                                   ["toEnum: bad argument"]

  fromEnum (UnsignedBV bv) = fromInteger (BV.asUnsigned bv)

instance KnownNat w => Ix (UnsignedBV w) where
  range (UnsignedBV loBV, UnsignedBV hiBV) =
    (UnsignedBV . mkBV knownNat) <$>
    [BV.asUnsigned loBV .. BV.asUnsigned hiBV]
  index (UnsignedBV loBV, UnsignedBV hiBV) (UnsignedBV ixBV) =
    index ( BV.asUnsigned loBV,
            BV.asUnsigned hiBV)
    (BV.asUnsigned ixBV)
  inRange (UnsignedBV loBV, UnsignedBV hiBV) (UnsignedBV ixBV) =
    inRange ( BV.asUnsigned loBV
            , BV.asUnsigned hiBV)
    (BV.asUnsigned ixBV)

instance KnownNat w => Bounded (UnsignedBV w) where
  minBound = UnsignedBV (BV.minUnsigned knownNat)
  maxBound = UnsignedBV (BV.maxUnsigned knownNat)

instance KnownNat w => Uniform (UnsignedBV w) where
  uniformM g = UnsignedBV <$> BV.uniformM knownNat g

instance UniformRange (UnsignedBV w) where
  uniformRM (UnsignedBV lo, UnsignedBV hi) g =
    UnsignedBV <$> BV.uUniformRM (lo, hi) g

instance KnownNat w => Random (UnsignedBV w)

-- Unsigned versions of BV operations that aren't captured by the various
-- instances provided above.

-- | The zero bitvector of any width.
zero :: NatRepr w -> UnsignedBV w
zero = UnsignedBV . BV.zero

-- | The bitvector with value 1, of any positive width.
one :: 1 <= w => NatRepr w -> UnsignedBV w
one = UnsignedBV . BV.one

-- | The bitvector whose value is its own width, of any width.
width :: NatRepr w -> UnsignedBV w
width = UnsignedBV . BV.width

-- | @clamp w i@ rounds @i@ to the nearest value between @0@ and @2^w - 1@
-- (inclusive).
clamp :: NatRepr w -> Integer -> UnsignedBV w
clamp w x = UnsignedBV (BV.unsignedClamp w x)

-- | Construct an 'UnsignedBV' from a 'Bool'.
bool :: Bool -> UnsignedBV 1
bool = UnsignedBV . BV.bool

-- | Construct an 'UnsignedBV' from a 'Word8'.
word8 :: Word8 -> UnsignedBV 8
word8 = UnsignedBV . BV.word8

-- | Construct an 'UnsignedBV' from a 'Word16'.
word16 :: Word16 -> UnsignedBV 16
word16 = UnsignedBV . BV.word16

-- | Construct an 'UnsignedBV' from a 'Word32'.
word32 :: Word32 -> UnsignedBV 32
word32 = UnsignedBV . BV.word32

-- | Construct an 'UnsignedBV' from a 'Word64'.
word64 :: Word64 -> UnsignedBV 64
word64 = UnsignedBV . BV.word64

-- | Construct an 'UnsignedBV' from a list of bits, in big endian order (bits
-- with lower value index in the list are mapped to higher order bits in the
-- output bitvector). Return the resulting 'UnsignedBV' along with its width.
--
-- >>> case BV.bitsBE [True, False] of p -> (fstPair p, sndPair p)
-- (2,UnsignedBV {asBV = BV 2})
bitsBE :: [Bool] -> Pair NatRepr UnsignedBV
bitsBE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bitsBE

-- | Construct an 'UnsignedBV' from a list of bits, in little endian order (bits
-- with lower value index in the list are mapped to lower order bits in the
-- output bitvector). Return the resulting 'UnsignedBV' along with its width.
--
-- >>> case BV.bitsLE [True, False] of p -> (fstPair p, sndPair p)
-- (2,UnsignedBV {asBV = BV 1})
bitsLE :: [Bool] -> Pair NatRepr UnsignedBV
bitsLE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bitsLE

-- | Construct an 'UnsignedBV' from a big-endian bytestring.
--
-- >>> case BV.bytestringBE (BS.pack [0, 1, 1]) of p -> (fstPair p, sndPair p)
-- (24,UnsignedBV {asBV = BV 257})
bytestringBE :: BS.ByteString -> Pair NatRepr UnsignedBV
bytestringBE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bytestringBE

-- | Construct an 'UnsignedBV' from a little-endian bytestring.
--
-- >>> case BV.bytestringLE (BS.pack [0, 1, 1]) of p -> (fstPair p, sndPair p)
-- (24,UnsignedBV {asBV = BV 65792})
bytestringLE :: BS.ByteString -> Pair NatRepr UnsignedBV
bytestringLE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bytestringLE

-- | Construct an 'UnsignedBV' from a list of bytes, in big endian order (bytes
-- with lower value index in the list are mapped to higher order bytes in the
-- output bitvector).
--
-- >>> case BV.bytesBE [0, 1, 1] of p -> (fstPair p, sndPair p)
-- (24,UnsignedBV {asBV = BV 257})
bytesBE :: [Word8] -> Pair NatRepr UnsignedBV
bytesBE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bytesBE

-- | Construct an 'UnsignedBV' from a list of bytes, in little endian order
-- (bytes with lower value index in the list are mapped to lower order bytes in
-- the output bitvector).
--
-- >>> case BV.bytesLE [0, 1, 1] of p -> (fstPair p, sndPair p)
-- (24,UnsignedBV {asBV = BV 65792})
bytesLE :: [Word8] -> Pair NatRepr UnsignedBV
bytesLE = viewPair (\w bv -> Pair w (UnsignedBV bv)) . BV.bytesLE

-- | Convert a bitvector to a list of bits, in big endian order
-- (higher order bits in the bitvector are mapped to lower indices in
-- the output list).
--
-- >>> BV.asBitsBE (knownNat @5) (BV.mkUnsignedBV knownNat 0b1101)
-- [False,True,True,False,True]
asBitsBE :: NatRepr w -> UnsignedBV w -> [Bool]
asBitsBE w (UnsignedBV bv) = BV.asBitsBE w bv

-- | Convert a bitvector to a list of bits, in little endian order
-- (lower order bits in the bitvector are mapped to lower indices in
-- the output list).
--
-- >>> BV.asBitsLE (knownNat @5) (BV.mkUnsignedBV knownNat 0b1101)
-- [True,False,True,True,False]
asBitsLE :: NatRepr w -> UnsignedBV w -> [Bool]
asBitsLE w (UnsignedBV bv) = BV.asBitsLE w bv

-- | Convert a bitvector to a list of bytes, in big endian order
-- (higher order bytes in the bitvector are mapped to lower indices in
-- the output list). Return 'Nothing' if the width is not a multiple
-- of 8.
--
-- >>> BV.asBytesBE (knownNat @32) (BV.mkUnsignedBV knownNat 0xaabbccdd)
-- Just [170,187,204,221]
asBytesBE :: NatRepr w -> UnsignedBV w -> Maybe [Word8]
asBytesBE w (UnsignedBV bv) = BV.asBytesBE w bv

-- | Convert a bitvector to a list of bytes, in little endian order
-- (lower order bytes in the bitvector are mapped to lower indices in
-- the output list). Return 'Nothing' if the width is not a multiple
-- of 8.
--
-- >>> BV.asBytesLE (knownNat @32) (BV.mkUnsignedBV knownNat 0xaabbccdd)
-- Just [221,204,187,170]
asBytesLE :: NatRepr w -> UnsignedBV w -> Maybe [Word8]
asBytesLE w (UnsignedBV bv) = BV.asBytesLE w bv

-- | 'asBytesBE', but for bytestrings.
asBytestringBE :: NatRepr w -> UnsignedBV w -> Maybe BS.ByteString
asBytestringBE w (UnsignedBV bv) = BV.asBytestringBE w bv

-- | 'asBytesLE', but for bytestrings.
asBytestringLE :: NatRepr w -> UnsignedBV w -> Maybe BS.ByteString
asBytestringLE w (UnsignedBV bv) = BV.asBytestringLE w bv

-- | Count trailing zeros in an 'UnsignedBV'.
ctz :: NatRepr w -> UnsignedBV w -> UnsignedBV w
ctz w (UnsignedBV bv) = UnsignedBV (BV.ctz w bv)

-- | Count leading zeros in an 'UnsignedBV'.
clz :: NatRepr w -> UnsignedBV w -> UnsignedBV w
clz w (UnsignedBV bv) = UnsignedBV (BV.clz w bv)

-- | Truncate a bitvector to a particular width given at runtime, while keeping
-- the type-level width constant.
truncBits :: Natural -> UnsignedBV w -> UnsignedBV w
truncBits b (UnsignedBV bv) = UnsignedBV (BV.truncBits b bv)

-- | Get the sign bit as an 'UnsignedBV'.
signBit :: 1 <= w => NatRepr w -> UnsignedBV w -> UnsignedBV w
signBit w (UnsignedBV bv) = UnsignedBV (BV.signBit w bv)

-- | Concatenate two bitvectors. The first argument gets placed in the
-- higher order bits.
--
-- >>> BV.concat knownNat knownNat (BV.mkUnsignedBV (knownNat @3) 0b001) (BV.mkUnsignedBV (knownNat @2) 0b10)
-- UnsignedBV {asBV = BV 6}
-- >>> :type it
-- it :: BV.UnsignedBV 5
concat :: NatRepr w
       -- ^ Width of higher-order bits
       -> NatRepr w'
       -- ^ Width of lower-order bits
       -> UnsignedBV w
       -- ^ Higher-order bits
       -> UnsignedBV w'
       -- ^ Lower-order bits
       -> UnsignedBV (w+w')
concat w w' (UnsignedBV hi) (UnsignedBV lo) = UnsignedBV (BV.concat w w' hi lo)

-- | Slice out a smaller bitvector from a larger one.
--
-- >>> BV.select (knownNat @1) (knownNat @4) (BV.mkUnsignedBV (knownNat @12) 0b110010100110)
-- UnsignedBV {asBV = BV 3}
-- >>> :type it
-- it :: BV.UnsignedBV 4
select :: ix + w' <= w
       => NatRepr ix
       -- ^ Index to start selecting from
       -> NatRepr w'
       -- ^ Desired output width
       -> UnsignedBV w
       -- ^ Bitvector to select from
       -> UnsignedBV w'
select ix w' (UnsignedBV bv) = UnsignedBV (BV.select ix w' bv)

-- | Like 'select', but takes a 'Natural' as the index to start
-- selecting from. Neither the index nor the output width is checked
-- to ensure the resulting 'BV' lies entirely within the bounds of the
-- original bitvector. Any bits "selected" from beyond the bounds of
-- the input bitvector will be 0.
--
-- >>> BV.select' 9 (knownNat @4) (BV.mkUnsignedBV (knownNat @12) 0b110010100110)
-- UnsignedBV {asBV = BV 6}
-- >>> :type it
-- it :: BV.UnsignedBV 4
select' :: Natural
        -- ^ Index to start selecting from
        -> NatRepr w'
        -- ^ Desired output width
        -> UnsignedBV w
        -- ^ Bitvector to select from
        -> UnsignedBV w'
select' ix w' (UnsignedBV bv) = UnsignedBV (BV.select' ix w' bv)

-- | Zero-extend a bitvector to one of strictly greater width.
--
-- >>> BV.zext (knownNat @8) (BV.mkUnsignedBV (knownNat @4) 0b1101)
-- UnsignedBV {asBV = BV 13}
-- >>> :type it
-- it :: BV.UnsignedBV 8
ext :: w + 1 <= w'
    => NatRepr w'
    -- ^ Desired output width
    -> UnsignedBV w
    -- ^ Bitvector to extend
    -> UnsignedBV w'
ext w (UnsignedBV bv) = UnsignedBV (BV.zext w bv)

-- | Truncate a bitvector to one of strictly smaller width.
trunc :: w' + 1 <= w
      => NatRepr w'
      -- ^ Desired output width
      -> UnsignedBV w
      -- ^ Bitvector to truncate
      -> UnsignedBV w'
trunc w' (UnsignedBV bv) = UnsignedBV (BV.trunc w' bv)

-- | Resizes a bitvector. If @w' > w@, perform a zero extension.
resize :: NatRepr w'
       -- ^ Desired output width
       -> UnsignedBV w
       -- ^ Bitvector to resize
       -> UnsignedBV w'
resize w' (UnsignedBV bv) = UnsignedBV (BV.zresize w' bv)

-- | Wide multiply of two bitvectors.
mulWide :: NatRepr w -> NatRepr w' -> UnsignedBV w -> UnsignedBV w' -> UnsignedBV (w+w')
mulWide w w' (UnsignedBV bv) (UnsignedBV bv') = UnsignedBV (BV.mulWide w w' bv bv')

----------------------------------------
-- Pretty printing

-- | Pretty print in hex
ppHex :: NatRepr w -> UnsignedBV w -> String
ppHex w (UnsignedBV bv) = BV.ppHex w bv

-- | Pretty print in binary
ppBin :: NatRepr w -> UnsignedBV w -> String
ppBin w (UnsignedBV bv) = BV.ppBin w bv

-- | Pretty print in octal
ppOct :: NatRepr w -> UnsignedBV w -> String
ppOct w (UnsignedBV bv) = BV.ppOct w bv

-- | Pretty print in decimal
ppDec :: NatRepr w -> UnsignedBV w -> String
ppDec w (UnsignedBV bv) = BV.ppDec w bv
