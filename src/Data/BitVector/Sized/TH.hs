{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-|
Module      : Data.BitVector.Sized.TH
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a quasiquoter for bitvectors, so you can write
things like: @[bv| 0010101 |]@, which gets converted into @21 :: BV
7@.
-}

module Data.BitVector.Sized.TH
  ( bv
  ) where

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Quote as TH

import Data.BitVector.Sized.Internal
import Data.Bits (shiftL)
import Data.Char (isSpace)
import Data.List (dropWhileEnd)

bv :: TH.QuasiQuoter
bv = TH.QuasiQuoter
  { TH.quoteExp = quoteBVExp
  , TH.quotePat = error "bv used as pattern"
  , TH.quoteType = error "bv used as type"
  , TH.quoteDec = error "bv used as declaration"
  }

binaryStringToInteger :: String -> Maybe Integer
binaryStringToInteger = helper . reverse
  where helper :: String -> Maybe Integer
        helper "0" = Just 0
        helper "1" = Just 1
        helper ('0':ds) = (`shiftL` 1) <$> helper ds
        helper ('1':ds) = ((1+) . (`shiftL` 1)) <$> helper ds
        helper _ = Nothing

quoteBVExp :: String -> TH.ExpQ
quoteBVExp s' =
  let s = trim s'
      w = length s
      mi = binaryStringToInteger s
  in case mi of
    Nothing -> error $ "Invalid bv: " <> s
    Just i' ->
      let i = truncBits w i'
      in [| BV i :: BV $(return $ TH.LitT (TH.NumTyLit (fromIntegral w))) |]
  where trim = dropWhileEnd isSpace . dropWhile isSpace
