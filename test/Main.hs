{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

-- Testing modules
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

-- Modules under test
import qualified Data.BitVector.Sized as BV

-- Auxiliary modules
import Control.Monad (when)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Numeric.Natural

max_width :: Natural
max_width = 32

min_int :: Integer
min_int = -(2 ^ max_width)

max_int :: Integer
max_int = 2 ^ max_width - 1

wellSized :: NatRepr w -> BV.BV w -> Bool
wellSized w (BV.BV x) = 0 <= x && x <= maxUnsigned w

mkBVProp :: Property
mkBVProp = property $ do
  Some w <- mkNatRepr <$> forAll (Gen.integral (Range.linear 0 max_width))
  x <- forAll (Gen.integral (Range.linear min_int max_int))
  let bv@(BV.BV _ x) = BV.mkBV w x
  when (not $ wellSized w bv) $ do
    footnote $ "Bad BV size: mkBV (knownNat @" <> show w <> ") " <> show x
    failure
  

tests :: TestTree
tests = testGroup "bv-sized tests"
  [ testProperty "mkBV" (withTests 500 $ mkBVProp) ]

main :: IO ()
main = defaultMain tests
