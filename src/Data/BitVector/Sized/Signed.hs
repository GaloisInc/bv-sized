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
import Data.Parameterized.WidthRepr

import Data.Bits
import Data.Ix
import GHC.Generics
import GHC.TypeLits

-- | Signed bit vector.
newtype SignedBV w = SignedBV (BV w)
  deriving (Generic, Show, Read, Eq)

instance KnownNat w => Ord (SignedBV w) where
  SignedBV bv1 `compare` SignedBV bv2 =
    if | bv1 == bv2             -> EQ
       | bvSlt knownWidth bv1 bv2 -> LT
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
  complement   = liftUnary (bvComplement knownWidth)
  shiftL       = liftBinaryInt (bvShl knownWidth)
  shiftR       = liftBinaryInt (bvAshr knownWidth)
  rotateL      = liftBinaryInt (bvRotateL knownWidth)
  rotateR      = liftBinaryInt (bvRotateR knownWidth)
  bitSize _    = widthInt (knownWidth @w)
  bitSizeMaybe _ = Just (widthInt (knownWidth @w))
  isSigned     = const True
  testBit (SignedBV bv) = bvTestBit bv
  bit          = SignedBV . mkBV knownWidth . (bit :: Int -> Integer)
  popCount (SignedBV bv) = bvPopCount bv

instance KnownNat w => FiniteBits (SignedBV w) where
  finiteBitSize _ = widthInt (knownWidth @w)

instance KnownNat w => Num (SignedBV w) where
  (+)         = liftBinary (bvAdd knownWidth)
  (*)         = liftBinary (bvMul knownWidth)
  abs         = liftUnary (bvAbs knownWidth)
  signum      = liftUnary (bvSignBit knownWidth)
  fromInteger = SignedBV . mkBV knownWidth
  negate      = liftUnary (bvNegate knownWidth)

checkInt :: WidthRepr w -> Int -> Int
checkInt w i | lo <= i && i <= hi = i
             | otherwise = error "bad argument"
  where lo = negate (bit (widthInt w - 1))
        hi = bit (widthInt w - 1) - 1

instance KnownNat w => Enum (SignedBV w) where
  toEnum = SignedBV . mkBV knownWidth . fromIntegral . checkInt (knownWidth @w)
  fromEnum (SignedBV bv) = fromIntegral (bvIntegerSigned (knownWidth @w) bv)

instance KnownNat w => Ix (SignedBV w) where
  range (SignedBV loBV, SignedBV hiBV) =
    (SignedBV . mkBV knownWidth) <$>
    [bvIntegerSigned knownWidth loBV .. bvIntegerSigned knownWidth hiBV]
  index (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    index ( bvIntegerSigned knownWidth loBV
          , bvIntegerSigned knownWidth hiBV)
    (bvIntegerSigned knownWidth ixBV)
  inRange (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
    inRange ( bvIntegerSigned knownWidth loBV
            , bvIntegerSigned knownWidth hiBV)
    (bvIntegerSigned knownWidth ixBV)

instance KnownNat w => Bounded (SignedBV w) where
  minBound = SignedBV (bvMinSigned knownWidth)
  maxBound = SignedBV (bvMaxSigned knownWidth)
