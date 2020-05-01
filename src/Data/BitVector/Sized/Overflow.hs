{-# LANGUAGE GADTs #-}

{-|
Module      : Data.BitVector.Sized.Overflow
Copyright   : (c) Galois Inc. 2020
License     : BSD-3
Maintainer  : Ben Selfridge <benselfridge@galois.com>
Stability   : experimental
Portability : portable

This module provides alternative definitions of certain bitvector
functions that might produce signed or unsigned overflow. Instead of
producing a pure value, these versions produce the same value along
with overflow flags.
-}

module Data.BitVector.Sized.Overflow
 ( UnsignedOverflow(..)
 , SignedOverflow(..)
 , Overflow(..)
 ) where

import Data.Parameterized ( NatRepr )
import qualified Data.Parameterized.NatRepr as P

import Data.BitVector.Sized.Internal

data UnsignedOverflow = UnsignedOverflow
                      | NoUnsignedOverflow

instance Semigroup UnsignedOverflow where
  NoUnsignedOverflow <> NoUnsignedOverflow = NoUnsignedOverflow
  _ <> _ = UnsignedOverflow

instance Monoid UnsignedOverflow where
  mempty = NoUnsignedOverflow

data SignedOverflow = SignedOverflow
                    | NoSignedOverflow

instance Semigroup SignedOverflow where
  NoSignedOverflow <> NoSignedOverflow = NoSignedOverflow
  _ <> _ = SignedOverflow

instance Monoid SignedOverflow where
  mempty = NoSignedOverflow

data Overflow a =
  Overflow UnsignedOverflow SignedOverflow a

instance Functor Overflow where
  fmap f (Overflow uof sof a) = Overflow uof sof (f a)

instance Applicative Overflow where
  pure a = Overflow mempty mempty a
  Overflow uof sof f <*> Overflow uof' sof' a =
    Overflow (uof <> uof') (sof <> sof') (f a)

instance Monad Overflow where
  Overflow uof sof a >>= k =
    let Overflow uof' sof' b = k a
    in Overflow (uof <> uof') (sof <> sof') b

unsignedOverflow :: NatRepr w -> Integer -> UnsignedOverflow
unsignedOverflow w res = if res < 0 || res > P.maxUnsigned w
                         then UnsignedOverflow
                         else NoUnsignedOverflow

signedOverflow :: NatRepr w -> Integer -> SignedOverflow
signedOverflow w res = case P.isZeroOrGT1 w of
  Left P.Refl -> NoSignedOverflow
  Right P.LeqProof -> if res < P.minSigned w || res > P.maxUnsigned w
                      then SignedOverflow
                      else NoSignedOverflow

liftBinaryOverflow :: NatRepr w
                   -> (Integer -> Integer -> Integer)
                   -> BV w -> BV w -> Overflow (BV w)
liftBinaryOverflow w op (BV x) (BV y) =
  let res = x `op` y
      uof = unsignedOverflow w res
      sof = signedOverflow w res
  in Overflow uof sof (mkBV w res)

