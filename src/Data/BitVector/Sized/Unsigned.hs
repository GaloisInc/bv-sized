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
Module      : Data.BitVector.Sized.Signed
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
  ) where

import           Data.BitVector.Sized.Internal (BV(..), mkBV)
import qualified Data.BitVector.Sized as BV
import Data.Parameterized.NatRepr

import Data.Bits (Bits(..), FiniteBits(..))
import Data.Ix
import GHC.Generics
import GHC.TypeLits
import Numeric.Natural

-- | Signed bit vector.
newtype UnsignedBV w = UnsignedBV (BV w)
  deriving (Generic, Show, Read, Eq, Ord)

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
liftBinaryInt op (UnsignedBV bv) i = UnsignedBV (op bv (fromIntegral i))

instance KnownNat w => Bits (UnsignedBV w) where
  (.&.)        = liftBinary BV.and
  (.|.)        = liftBinary BV.or
  xor          = liftBinary BV.xor
  complement   = liftUnary (BV.complement knownNat)
  shiftL       = liftBinaryInt (BV.shl knownNat)
  shiftR       = liftBinaryInt BV.lshr
  rotateL      = liftBinaryInt (BV.rotateL knownNat)
  rotateR      = liftBinaryInt (BV.rotateR knownNat)
  bitSize _    = widthVal (knownNat @w)
  bitSizeMaybe _ = Just (widthVal (knownNat @w))
  isSigned     = const False
  testBit (UnsignedBV bv) = BV.testBit' bv . fromIntegral
  bit          = UnsignedBV . BV.bit' knownNat . fromIntegral
  popCount (UnsignedBV bv) = fromIntegral (BV.popCount bv)

instance KnownNat w => FiniteBits (UnsignedBV w) where
  finiteBitSize _ = widthVal (knownNat @w)

instance KnownNat w => Num (UnsignedBV w) where
  (+)         = liftBinary (BV.add knownNat)
  (*)         = liftBinary (BV.mul knownNat)
  abs         = liftUnary (BV.abs knownNat)
  signum      = const $ UnsignedBV (BV 0)
  fromInteger = UnsignedBV . mkBV knownNat
  -- in this case, negate just means "additive inverse"
  negate      = liftUnary (BV.negate knownNat)

checkInt :: NatRepr w -> Int -> Int
checkInt w i | 0 <= i && i <= fromIntegral (maxUnsigned w) = i
             | otherwise = error "bad argument"

instance KnownNat w => Enum (UnsignedBV w) where
  toEnum   = UnsignedBV . mkBV knownNat . fromIntegral . checkInt (knownNat @w)
  fromEnum (UnsignedBV bv) = fromIntegral (BV.asUnsigned bv)

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
  minBound = UnsignedBV BV.minUnsigned
  maxBound = UnsignedBV (BV.maxUnsigned knownNat)
