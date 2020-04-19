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

import Data.BitVector.Sized

import Data.Bits
import Data.Ix
import Data.Parameterized
import GHC.Generics
import GHC.TypeLits

-- | Signed bit vector.
newtype SignedBV w = SignedBV (BV w)
  deriving (Generic, Show, Read, Eq)

instance KnownNat w => Ord (SignedBV w) where
  SignedBV bv1 `compare` SignedBV bv2 =
    if | bv1 == bv2             -> EQ
       | bvSlt knownNat bv1 bv2 -> LT
       | otherwise              -> GT

liftUnary :: (BV w -> BV w)
          -> SignedBV w
          -> SignedBV w
liftUnary op (SignedBV bv) = SignedBV (op bv)

liftBinary :: (BV w -> BV w -> BV w)
           -> SignedBV w
           -> SignedBV w
           -> SignedBV w
liftBinary op (SignedBV bv1) (SignedBV bv2) = SignedBV (op bv1 bv2)

liftBinaryInt :: (BV w -> Int -> BV w)
              -> SignedBV w
              -> Int
              -> SignedBV w
liftBinaryInt op (SignedBV bv) i = SignedBV (op bv i)  

instance KnownNat w => Bits (SignedBV w) where
  (.&.)        = liftBinary bvAnd
  (.|.)        = liftBinary bvOr
  xor          = liftBinary bvXor
  complement   = liftUnary (bvComplement knownNat)
  shiftL       = liftBinaryInt (bvShl knownNat)
  shiftR       = liftBinaryInt (bvAshr knownNat)
  rotateL      = liftBinaryInt (bvRotateL knownNat)
  rotateR      = liftBinaryInt (bvRotateR knownNat)
  bitSize _    = fromIntegral (intValue (knownNat @w))
  bitSizeMaybe _ = Just (fromIntegral (intValue (knownNat @w)))
  isSigned     = const True
  testBit (SignedBV bv) = bvTestBit bv
  bit          = SignedBV . mkBV knownNat . (bit :: Int -> Integer)
  popCount (SignedBV bv) = bvPopCount bv

instance KnownNat w => FiniteBits (SignedBV w) where
  finiteBitSize _ = fromIntegral (intValue (knownNat @w))

instance KnownNat w => Num (SignedBV w) where
  (+)         = liftBinary (bvAdd knownNat)
  (*)         = liftBinary (bvMul knownNat)
  abs         = liftUnary (bvAbs knownNat)
  signum      = liftUnary (bvSignBit knownNat)
  fromInteger = SignedBV . mkBV knownNat
  negate      = liftUnary (bvNegate knownNat)

checkInt :: NatRepr w -> Int -> Int
checkInt w i | lo <= i && i <= hi = i
             | otherwise = error "bad argument"
  where lo = negate (bit (widthVal w - 1))
        hi = bit (widthVal w - 1) - 1

instance KnownNat w => Enum (SignedBV w) where
  toEnum = SignedBV . mkBV knownNat . fromIntegral . checkInt (knownNat @w)
  fromEnum (SignedBV bv) = fromIntegral (bvIntegerSigned (knownNat @w) bv)

instance KnownNat w => Ix (SignedBV w) where
  range (SignedBV loBV, SignedBV hiBV) =
    (SignedBV . mkBV knownNat) <$>
    [bvIntegerSigned knownNat loBV .. bvIntegerSigned knownNat hiBV]
  index (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    index ( bvIntegerSigned knownNat loBV
          , bvIntegerSigned knownNat hiBV)
    (bvIntegerSigned knownNat ixBV)
  inRange (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    inRange ( bvIntegerSigned knownNat loBV
            , bvIntegerSigned knownNat hiBV)
    (bvIntegerSigned knownNat ixBV)

instance KnownNat w => Bounded (SignedBV w) where
  minBound = SignedBV (bvMinSigned knownNat)
  maxBound = SignedBV (bvMaxSigned knownNat)
