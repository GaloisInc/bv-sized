{-# LANGUAGE DataKinds #-}

module Main where

import Test.QuickCheck

import Data.BitVector.Sized

main :: IO ()
main = quickCheck bitVectorTest

bitVectorTest :: BitVector 64 -> Bool
bitVectorTest bv = bitVector (bvIntegerS bv) == bv
