{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import GHC.TypeLits
import Test.QuickCheck

import Data.BitVector.Sized

main :: IO ()
main = quickCheck bitVectorTest

bitVectorTest :: BitVector 64 -> Bool
bitVectorTest bv = bitVector (bvIntegerS bv) == bv


instance KnownNat w => Arbitrary (BitVector w) where
  arbitrary = choose (minBound, maxBound)
