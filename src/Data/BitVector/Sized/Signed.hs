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

This module defines a wrapper around the 'BV' type, 'SignedBV', with
instances not provided by 'BV'.
-}

module Data.BitVector.Sized.Signed
  ( SignedBV
  ) where

import Data.BitVector.Sized

import Data.Bits
import Data.Parameterized
import GHC.Generics
import GHC.TypeLits

-- | Signed bit vector.
newtype SignedBV w = SignedBV (BV w)
  deriving (Generic, Show, Read, Eq, Ord)

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
  shift        = liftBinaryInt (bvShift knownNat)
  rotate       = liftBinaryInt (bvRotate knownNat)
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
  signum      = liftUnary (bvSignum knownNat)
  fromInteger = SignedBV . mkBV knownNat
  negate      = liftUnary (bvNegate knownNat)

instance KnownNat w => Enum (SignedBV w) where
  toEnum   = SignedBV . mkBV knownNat . fromIntegral
  fromEnum (SignedBV bv) = fromIntegral (bvIntegerUnsigned bv)

-- instance KnownNat w => Ix (SignedBV w) where
--   range (SignedBV loBV, SignedBV hiBV) =
--     (SignedBV . mkBV knownNat) <$> [bvNatural loBV .. bvNatural hiBV]
--   index (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
--     index (bvNatural loBV, bvNatural hiBV) (bvNatural ixBV)
--   inRange (SignedBV loBV, SignedBV hiBV) (SignedBV ixBV) =
--     inRange (bvNatural loBV, bvNatural hiBV) (bvNatural ixBV)

-- instance KnownNat w => Bounded (BitVector w) where
--   minBound = bitVector (0 :: Integer)
--   maxBound = bitVector ((-1) :: Integer)

-- instance KnownNat w => Arbitrary (BitVector w) where
--   arbitrary = choose (minBound, maxBound)

-- instance KnownNat w => Random (BitVector w) where
--   randomR (bvLo, bvHi) gen =
--     let (x, gen') = randomR (bvNatural bvLo, bvNatural bvHi) gen
--     in (bitVector x, gen')
--   random gen =
--     let (x :: Integer, gen') = random gen
--     in (bitVector x, gen')

-- prettyHex :: (Integral a, PrintfArg a, Show a) => a -> Integer -> String
-- prettyHex width val = printf format val width
--   where -- numDigits = (width+3) `quot` 4
--         -- format = "0x%." ++ show numDigits ++ "x<%d>"
--         format = "0x%x<%d>"

-- instance Pretty (BitVector w) where
--   -- | Pretty print a bit vector (shows its width)
--   pPrint (BV wRepr x) = text $ prettyHex (natValue wRepr) x
