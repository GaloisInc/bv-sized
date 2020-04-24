{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  ) where

import           Data.BitVector.Sized (BV, mkBV)
import qualified Data.BitVector.Sized.Internal as BV
import Data.Parameterized.NatRepr

import Data.Bits (Bits(..), FiniteBits(..))
import Data.Ix
import GHC.Generics
import GHC.TypeLits
import Numeric.Natural

-- | Signed bit vector.
newtype SignedBV w = SignedBV (BV w)
  deriving (Generic, Show, Read, Eq)

instance KnownNat w => Ord (SignedBV w) where
  SignedBV bv1 `compare` SignedBV bv2 =
    if | bv1 == bv2              -> EQ
       | BV.slt knownNat bv1 bv2 -> LT
       | otherwise               -> GT

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
liftBinaryInt op (SignedBV bv) i = SignedBV (op bv (fromIntegral i))

instance KnownNat w => Bits (SignedBV w) where
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
  testBit (SignedBV bv) = BV.testBit' bv . fromIntegral
  bit          = SignedBV . BV.bit' knownNat . fromIntegral
  popCount (SignedBV bv) = BV.naturalToInt (BV.asNatural (BV.popCount bv))

instance KnownNat w => FiniteBits (SignedBV w) where
  finiteBitSize _ = widthVal (knownNat @w)

instance (KnownNat w, 1 <= w) => Num (SignedBV w) where
  (+)         = liftBinary (BV.add knownNat)
  (*)         = liftBinary (BV.mul knownNat)
  abs         = liftUnary (BV.abs knownNat)
  signum      = liftUnary (BV.signBit knownNat)
  fromInteger = SignedBV . mkBV knownNat
  negate      = liftUnary (BV.negate knownNat)

checkInt :: NatRepr w -> Int -> Int
checkInt w i | lo <= i && i <= hi = i
             | otherwise = error "bad argument"
  where lo = negate (bit (widthVal w - 1))
        hi = bit (widthVal w - 1) - 1

instance KnownNat w => Enum (SignedBV w) where
  toEnum = SignedBV . mkBV knownNat . fromIntegral . checkInt (knownNat @w)
  fromEnum (SignedBV bv) = fromIntegral (BV.asSigned (knownNat @w) bv)

instance KnownNat w => Ix (SignedBV w) where
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
