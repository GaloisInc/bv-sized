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

import Data.BitVector.Sized.Internal
import Data.Parameterized.NatRepr

import Data.Bits
import Data.Ix
import GHC.Generics
import GHC.TypeLits

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

liftBinaryInt :: (BV w -> Int -> BV w)
              -> UnsignedBV w
              -> Int
              -> UnsignedBV w
liftBinaryInt op (UnsignedBV bv) i = UnsignedBV (op bv i)

instance KnownNat w => Bits (UnsignedBV w) where
  (.&.)        = liftBinary bvAnd
  (.|.)        = liftBinary bvOr
  xor          = liftBinary bvXor
  complement   = liftUnary (bvComplement knownNat)
  shiftL       = liftBinaryInt (bvShl knownNat)
  shiftR       = liftBinaryInt bvLshr
  rotateL      = liftBinaryInt (bvRotateL knownNat)
  rotateR      = liftBinaryInt (bvRotateR knownNat)
  bitSize _    = widthVal (knownNat @w)
  bitSizeMaybe _ = Just (widthVal (knownNat @w))
  isSigned     = const False
  testBit (UnsignedBV bv) = bvTestBit bv
  bit          = UnsignedBV . mkBV knownNat . (bit :: Int -> Integer)
  popCount (UnsignedBV bv) = bvPopCount bv

instance KnownNat w => FiniteBits (UnsignedBV w) where
  finiteBitSize _ = widthVal (knownNat @w)

instance KnownNat w => Num (UnsignedBV w) where
  (+)         = liftBinary (bvAdd knownNat)
  (*)         = liftBinary (bvMul knownNat)
  abs         = liftUnary (bvAbs knownNat)
  signum      = const $ UnsignedBV (BV 0)
  fromInteger = UnsignedBV . mkBV knownNat
  -- in this case, negate just means "additive inverse"
  negate      = liftUnary (bvNegate knownNat)

checkInt :: NatRepr w -> Int -> Int
checkInt w i | 0 <= i && i <= fromIntegral (maxUnsigned w) = i
             | otherwise = error "bad argument"

instance KnownNat w => Enum (UnsignedBV w) where
  toEnum   = UnsignedBV . mkBV knownNat . fromIntegral . checkInt (knownNat @w)
  fromEnum (UnsignedBV bv) = fromIntegral (bvIntegerUnsigned bv)

instance KnownNat w => Ix (UnsignedBV w) where
  range (UnsignedBV loBV, UnsignedBV hiBV) =
    (UnsignedBV . mkBV knownNat) <$>
    [bvIntegerUnsigned loBV .. bvIntegerUnsigned hiBV]
  index (UnsignedBV loBV, UnsignedBV hiBV) (UnsignedBV ixBV) =
    index ( bvIntegerUnsigned loBV
          , bvIntegerUnsigned hiBV)
    (bvIntegerUnsigned ixBV)
  inRange (UnsignedBV loBV, UnsignedBV hiBV) (UnsignedBV ixBV) =
    inRange ( bvIntegerUnsigned loBV
            , bvIntegerUnsigned hiBV)
    (bvIntegerUnsigned ixBV)

instance KnownNat w => Bounded (UnsignedBV w) where
  minBound = UnsignedBV bvMinUnsigned
  maxBound = UnsignedBV (bvMaxUnsigned knownNat)
