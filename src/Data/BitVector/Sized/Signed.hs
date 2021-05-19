{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Data.BitVector.Sized.Signed
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a wrapper around the 'BV' type, 'SignedBV', with
instances not provided by 'BV'.
-}

module Data.BitVector.Sized.Signed
  ( SignedBV(..)
    -- * Constructors
  , mkSignedBV, mkSignedBV'
  , clamp
  , zero, one, width
    -- * Construction from fixed-width data types
  , bool, int8, int16, int32, int64
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

import           Data.BitVector.Sized (BV, mkBV)
import qualified Data.BitVector.Sized.Internal as BV
import           Data.BitVector.Sized.Panic (panic)
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
  ( NatRepr
  , knownNat
  , widthVal
  , minSigned
  , maxSigned
  , LeqProof(..)
  , isPosNat
  , leqAddPos
  , addIsLeq
  , leqTrans
  )
import Data.Parameterized.Pair

import Data.Bits (Bits(..), FiniteBits(..))
import qualified Data.ByteString as BS
import Data.Int
import Data.Ix (Ix(inRange, range, index))
import Data.Word
import GHC.Generics (Generic)
import GHC.TypeLits (KnownNat, type (<=), type (+))
import Numeric.Natural (Natural)
import Prelude hiding (concat)
import System.Random
import System.Random.Stateful

-- | Signed bit vector.
data SignedBV w where
  SignedBV :: 1 <= w => { asBV :: BV w } -> SignedBV w
  -- deriving (Generic, Show, Read, Eq)

-- deriving instance Generic (SignedBV w)
deriving instance Show (SignedBV w)
deriving instance 1 <= w => Read (SignedBV w)
deriving instance Eq (SignedBV w)

instance (KnownNat w, 1 <= w) => Ord (SignedBV w) where
  SignedBV bv1 `compare` SignedBV bv2 =
    if | bv1 == bv2              -> EQ
       | BV.slt knownNat bv1 bv2 -> LT
       | otherwise               -> GT

instance ShowF SignedBV

-- | Convenience wrapper for 'BV.mkBV'.
mkSignedBV :: 1 <= w => NatRepr w -> Integer -> SignedBV w
mkSignedBV w x = SignedBV (BV.mkBV w x)

-- | Convenience wrapper for 'BV.mkBVSigned'.
mkSignedBV' :: 1 <= w => NatRepr w -> Integer -> Maybe (SignedBV w)
mkSignedBV' w x = SignedBV <$> BV.mkBVSigned w x

liftUnary :: (BV w -> BV w)
          -> SignedBV w
          -> SignedBV w
liftUnary op (SignedBV bv) = SignedBV (op bv)

liftBinary :: (BV w -> BV w -> BV w)
           -> SignedBV w
           -> SignedBV w
           -> SignedBV w
liftBinary op (SignedBV bv1) (SignedBV bv2) = SignedBV (op bv1 bv2)

liftBinaryInt :: (BV w -> Natural -> BV w)
              -> SignedBV w
              -> Int
              -> SignedBV w
liftBinaryInt op (SignedBV bv) i = SignedBV (op bv (intToNatural i))

intToNatural :: Int -> Natural
intToNatural = fromIntegral

instance (KnownNat w, 1 <= w) => Bits (SignedBV w) where
  (.&.)        = liftBinary BV.and
  (.|.)        = liftBinary BV.or
  xor          = liftBinary BV.xor
  complement   = liftUnary (BV.complement knownNat)
  shiftL       = liftBinaryInt (BV.shl knownNat)
  shiftR       = liftBinaryInt (BV.ashr knownNat)
  rotateL      = liftBinaryInt (BV.rotateL knownNat)
  rotateR      = liftBinaryInt (BV.rotateR knownNat)
  bitSize _    = widthVal (knownNat @w)
  bitSizeMaybe _ = Just (widthVal (knownNat @w))
  isSigned     = const True
  testBit (SignedBV bv) ix = BV.testBit' (intToNatural ix) bv
  bit          = SignedBV . BV.bit' knownNat . intToNatural
  popCount (SignedBV bv) = fromInteger (BV.asUnsigned (BV.popCount bv))

instance (KnownNat w, 1 <= w) => FiniteBits (SignedBV w) where
  finiteBitSize _ = widthVal (knownNat @w)
  countLeadingZeros  (SignedBV bv) = fromInteger $ BV.asUnsigned $ BV.clz knownNat bv
  countTrailingZeros (SignedBV bv) = fromInteger $ BV.asUnsigned $ BV.ctz knownNat bv

instance (KnownNat w, 1 <= w) => Num (SignedBV w) where
  (+)         = liftBinary (BV.add knownNat)
  (*)         = liftBinary (BV.mul knownNat)
  abs         = liftUnary (BV.abs knownNat)
  signum (SignedBV bv) = mkSignedBV knownNat $ signum $ BV.asSigned knownNat bv
  fromInteger = SignedBV . mkBV knownNat
  negate      = liftUnary (BV.negate knownNat)

instance (KnownNat w, 1 <= w) => Real (SignedBV w) where
  toRational (SignedBV bv) = fromInteger (BV.asSigned knownNat bv)

instance (KnownNat w, 1 <= w) => Integral (SignedBV w) where
  toInteger (SignedBV bv) = BV.asSigned knownNat bv
  SignedBV bv `quotRem` SignedBV bv' =
    let (q, r) = BV.squotRem knownNat bv bv'
    in (SignedBV q, SignedBV r)

instance (KnownNat w, 1 <= w) => Enum (SignedBV w) where
  toEnum = SignedBV . mkBV knownNat . checkInt
    where checkInt i | lo <= toInteger i && toInteger i <= hi = toInteger i
                     | otherwise = panic "Data.BitVector.Sized.Signed"
                                   ["toEnum: bad argument"]
            where lo = minSigned (knownNat @w)
                  hi = maxSigned (knownNat @w)

  fromEnum (SignedBV bv) = fromInteger (BV.asSigned (knownNat @w) bv)

instance (KnownNat w, 1 <= w) => Ix (SignedBV w) where
  range (SignedBV loBV, SignedBV hiBV) =
    (SignedBV . mkBV knownNat) <$>
    [BV.asSigned knownNat loBV .. BV.asSigned knownNat hiBV]
  index (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    index ( BV.asSigned knownNat loBV
          , BV.asSigned knownNat hiBV)
    (BV.asSigned knownNat ixBV)
  inRange (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    inRange ( BV.asSigned knownNat loBV
            , BV.asSigned knownNat hiBV)
    (BV.asSigned knownNat ixBV)

instance (KnownNat w, 1 <= w) => Bounded (SignedBV w) where
  minBound = SignedBV (BV.minSigned knownNat)
  maxBound = SignedBV (BV.maxSigned knownNat)

instance (KnownNat w, 1 <= w) => Uniform (SignedBV w) where
  uniformM g = SignedBV <$> BV.uniformM knownNat g

instance (KnownNat w, 1 <= w) => UniformRange (SignedBV w) where
  uniformRM (SignedBV lo, SignedBV hi) g =
    SignedBV <$> BV.sUniformRM knownNat (lo, hi) g

instance (KnownNat w, 1 <= w) => Random (SignedBV w)

-- Signed versions of BV operations that aren't captured by the various
-- instances provided above.

-- | The zero bitvector of any width.
zero :: 1 <= w => NatRepr w -> SignedBV w
zero = SignedBV . BV.zero

-- | The bitvector with value 1, of any positive width.
one :: 1 <= w => NatRepr w -> SignedBV w
one = SignedBV . BV.one

-- | The bitvector whose value is its own width, of any width.
width :: 1 <= w => NatRepr w -> SignedBV w
width = SignedBV . BV.width

-- | @clamp w i@ rounds @i@ to the nearest value between @0@ and @2^w - 1@
-- (inclusive).
clamp :: 1 <= w => NatRepr w -> Integer -> SignedBV w
clamp w x = SignedBV (BV.signedClamp w x)

-- | Construct an 'SignedBV' from a 'Bool'.
bool :: Bool -> SignedBV 1
bool = SignedBV . BV.bool

-- | Construct an 'SignedBV' from an 'Int8'.
int8 :: Int8 -> SignedBV 8
int8 = SignedBV . BV.int8

-- | Construct an 'SignedBV' from a 'Int16'.
int16 :: Int16 -> SignedBV 16
int16 = SignedBV . BV.int16

-- | Construct an 'SignedBV' from a 'Int32'.
int32 :: Int32 -> SignedBV 32
int32 = SignedBV . BV.int32

-- | Construct an 'SignedBV' from a 'Int64'.
int64 :: Int64 -> SignedBV 64
int64 = SignedBV . BV.int64

-- | Construct an 'SignedBV' from a list of bits, in big endian order (bits with
-- lower value index in the list are mapped to higher order bits in the output
-- bitvector). Return the resulting 'SignedBV' along with its width.
--
-- >>> case BV.bitsBE [True, False] of p -> (fstPair p, sndPair p)
-- (2,SignedBV {asBV = BV 2})
bitsBE :: [Bool] -> Maybe (Pair NatRepr SignedBV)
bitsBE bs = case BV.bitsBE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Construct an 'SignedBV' from a list of bits, in little endian order (bits
-- with lower value index in the list are mapped to lower order bits in the
-- output bitvector). Return the resulting 'SignedBV' along with its width.
--
-- >>> case BV.bitsLE [True, False] of p -> (fstPair p, sndPair p)
-- (2,SignedBV {asBV = BV 1})
bitsLE :: [Bool] -> Maybe (Pair NatRepr SignedBV)
bitsLE bs = case BV.bitsBE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Construct an 'SignedBV' from a big-endian bytestring.
--
-- >>> case BV.bytestringBE (BS.pack [0, 1, 1]) of p -> (fstPair p, sndPair p)
-- (24,SignedBV {asBV = BV 257})
bytestringBE :: BS.ByteString -> Maybe (Pair NatRepr SignedBV)
bytestringBE bs = case BV.bytestringBE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Construct an 'SignedBV' from a little-endian bytestring.
--
-- >>> case BV.bytestringLE (BS.pack [0, 1, 1]) of p -> (fstPair p, sndPair p)
-- (24,SignedBV {asBV = BV 65792})
bytestringLE :: BS.ByteString -> Maybe (Pair NatRepr SignedBV)
bytestringLE bs = case BV.bytestringLE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Construct an 'SignedBV' from a list of bytes, in big endian order (bytes
-- with lower value index in the list are mapped to higher order bytes in the
-- output bitvector).
--
-- >>> case BV.bytesBE [0, 1, 1] of p -> (fstPair p, sndPair p)
-- (24,SignedBV {asBV = BV 257})
bytesBE :: [Word8] -> Maybe (Pair NatRepr SignedBV)
bytesBE bs = case BV.bytesBE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Construct an 'SignedBV' from a list of bytes, in little endian order
-- (bytes with lower value index in the list are mapped to lower order bytes in
-- the output bitvector).
--
-- >>> case BV.bytesLE [0, 1, 1] of p -> (fstPair p, sndPair p)
-- (24,SignedBV {asBV = BV 65792})
bytesLE :: [Word8] -> Maybe (Pair NatRepr SignedBV)
bytesLE bs = case BV.bytesLE bs of
  Pair w bv | Just LeqProof <- isPosNat w -> Just (Pair w (SignedBV bv))
  _ -> Nothing

-- | Convert a bitvector to a list of bits, in big endian order
-- (higher order bits in the bitvector are mapped to lower indices in
-- the output list).
--
-- >>> BV.asBitsBE (knownNat @5) (BV.mkSignedBV knownNat 0b1101)
-- [False,True,True,False,True]
asBitsBE :: NatRepr w -> SignedBV w -> [Bool]
asBitsBE w (SignedBV bv) = BV.asBitsBE w bv

-- | Convert a bitvector to a list of bits, in little endian order
-- (lower order bits in the bitvector are mapped to lower indices in
-- the output list).
--
-- >>> BV.asBitsLE (knownNat @5) (BV.mkSignedBV knownNat 0b1101)
-- [True,False,True,True,False]
asBitsLE :: NatRepr w -> SignedBV w -> [Bool]
asBitsLE w (SignedBV bv) = BV.asBitsLE w bv

-- | Convert a bitvector to a list of bytes, in big endian order
-- (higher order bytes in the bitvector are mapped to lower indices in
-- the output list). Return 'Nothing' if the width is not a multiple
-- of 8.
--
-- >>> BV.asBytesBE (knownNat @32) (BV.mkSignedBV knownNat 0xaabbccdd)
-- Just [170,187,204,221]
asBytesBE :: NatRepr w -> SignedBV w -> Maybe [Word8]
asBytesBE w (SignedBV bv) = BV.asBytesBE w bv

-- | Convert a bitvector to a list of bytes, in little endian order
-- (lower order bytes in the bitvector are mapped to lower indices in
-- the output list). Return 'Nothing' if the width is not a multiple
-- of 8.
--
-- >>> BV.asBytesLE (knownNat @32) (BV.mkSignedBV knownNat 0xaabbccdd)
-- Just [221,204,187,170]
asBytesLE :: NatRepr w -> SignedBV w -> Maybe [Word8]
asBytesLE w (SignedBV bv) = BV.asBytesLE w bv

-- | 'asBytesBE', but for bytestrings.
asBytestringBE :: NatRepr w -> SignedBV w -> Maybe BS.ByteString
asBytestringBE w (SignedBV bv) = BV.asBytestringBE w bv

-- | 'asBytesLE', but for bytestrings.
asBytestringLE :: NatRepr w -> SignedBV w -> Maybe BS.ByteString
asBytestringLE w (SignedBV bv) = BV.asBytestringLE w bv

-- | Count trailing zeros in an 'SignedBV'.
ctz :: NatRepr w -> SignedBV w -> SignedBV w
ctz w (SignedBV bv) = SignedBV (BV.ctz w bv)

-- | Count leading zeros in an 'SignedBV'.
clz :: NatRepr w -> SignedBV w -> SignedBV w
clz w (SignedBV bv) = SignedBV (BV.clz w bv)

-- | Truncate a bitvector to a particular width given at runtime, while keeping
-- the type-level width constant.
truncBits :: Natural -> SignedBV w -> SignedBV w
truncBits b (SignedBV bv) = SignedBV (BV.truncBits b bv)

-- | Get the sign bit as an 'SignedBV'.
signBit :: 1 <= w => NatRepr w -> SignedBV w -> SignedBV w
signBit w (SignedBV bv) = SignedBV (BV.signBit w bv)

-- | Concatenate two bitvectors. The first argument gets placed in the
-- higher order bits.
--
-- >>> BV.concat knownNat knownNat (BV.mkSignedBV (knownNat @3) 0b001) (BV.mkSignedBV (knownNat @2) 0b10)
-- SignedBV {asBV = BV 6}
-- >>> :type it
-- it :: BV.SignedBV 5
concat :: NatRepr w
       -- ^ Width of higher-order bits
       -> NatRepr w'
       -- ^ Width of lower-order bits
       -> SignedBV w
       -- ^ Higher-order bits
       -> SignedBV w'
       -- ^ Lower-order bits
       -> SignedBV (w+w')
concat w w' (SignedBV hi) (SignedBV lo)
  | LeqProof <- w `leqAddPos` w' = SignedBV (BV.concat w w' hi lo)

-- | Slice out a smaller bitvector from a larger one.
--
-- >>> BV.select (knownNat @1) (knownNat @4) (BV.mkSignedBV (knownNat @12) 0b110010100110)
-- SignedBV {asBV = BV 3}
-- >>> :type it
-- it :: BV.SignedBV 4
select :: (1 <= w', ix + w' <= w)
       => NatRepr ix
       -- ^ Index to start selecting from
       -> NatRepr w'
       -- ^ Desired output width
       -> SignedBV w
       -- ^ Bitvector to select from
       -> SignedBV w'
select ix w' (SignedBV bv) = SignedBV (BV.select ix w' bv)

-- | Like 'select', but takes a 'Natural' as the index to start
-- selecting from. Neither the index nor the output width is checked
-- to ensure the resulting 'BV' lies entirely within the bounds of the
-- original bitvector. Any bits "selected" from beyond the bounds of
-- the input bitvector will be 0.
--
-- >>> BV.select' 9 (knownNat @4) (BV.mkSignedBV (knownNat @12) 0b110010100110)
-- SignedBV {asBV = BV 6}
-- >>> :type it
-- it :: BV.SignedBV 4
select' :: 1 <= w'
        => Natural
        -- ^ Index to start selecting from
        -> NatRepr w'
        -- ^ Desired output width
        -> SignedBV w
        -- ^ Bitvector to select from
        -> SignedBV w'
select' ix w' (SignedBV bv) = SignedBV (BV.select' ix w' bv)

-- | Sign-extend a bitvector to one of strictly greater width.
--
-- >>> BV.ext (knownNat @8) (BV.mkSignedBV (knownNat @4) 0b1101)
-- SignedBV {asBV = BV 253}
-- >>> :type it
-- it :: BV.SignedBV 8
ext :: forall w w' . w + 1 <= w'
    => NatRepr w
    -- ^ Width of input bitvector
    -> NatRepr w'
    -- ^ Desired output width
    -> SignedBV w
    -- ^ Bitvector to extend
    -> SignedBV w'
ext w w' (SignedBV bv)
  | w_lt_w_plus_1@LeqProof <- addIsLeq w (knownNat @1)
  , one_lt_w_plus_1@LeqProof <- leqTrans (LeqProof @1 @w) w_lt_w_plus_1
  , LeqProof <- leqTrans one_lt_w_plus_1 (LeqProof @(w+1) @w')
  = SignedBV (BV.sext w w' bv)

-- | Truncate a bitvector to one of strictly smaller width.
trunc :: (1 <= w', w' + 1 <= w)
      => NatRepr w'
      -- ^ Desired output width
      -> SignedBV w
      -- ^ Bitvector to truncate
      -> SignedBV w'
trunc w' (SignedBV bv) = SignedBV (BV.trunc w' bv)

-- | Resizes a bitvector. If @w' > w@, perform a sign extension.
resize :: 1 <= w'
       => NatRepr w
       -- ^ Width of input vector
       -> NatRepr w'
       -- ^ Desired output width
       -> SignedBV w
       -- ^ Bitvector to resize
       -> SignedBV w'
resize w w' (SignedBV bv) = SignedBV (BV.sresize w w' bv)

-- | Wide multiply of two bitvectors.
mulWide :: NatRepr w -> NatRepr w' -> SignedBV w -> SignedBV w' -> SignedBV (w+w')
mulWide w w' (SignedBV bv) (SignedBV bv')
  | LeqProof <- w `leqAddPos` w' = SignedBV (BV.mulWide w w' bv bv')

----------------------------------------
-- Pretty printing

-- | Pretty print in hex
ppHex :: NatRepr w -> SignedBV w -> String
ppHex w (SignedBV bv) = BV.ppHex w bv

-- | Pretty print in binary
ppBin :: NatRepr w -> SignedBV w -> String
ppBin w (SignedBV bv) = BV.ppBin w bv

-- | Pretty print in octal
ppOct :: NatRepr w -> SignedBV w -> String
ppOct w (SignedBV bv) = BV.ppOct w bv

-- | Pretty print in decimal
ppDec :: NatRepr w -> SignedBV w -> String
ppDec w (SignedBV bv) = BV.ppDec w bv
