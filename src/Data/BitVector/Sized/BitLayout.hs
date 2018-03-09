{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.BitLayout
Copyright   : (c) Benjamin Selfridge, 2018
                  Galois Inc.
License     : BSD3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a 'BitLayout' datatype which encodes a chunk-to-chunk mapping
from a smaller bit vector into a larger one.
-}

module Data.BitVector.Sized.BitLayout where

import Data.Parameterized
import qualified Data.Sequence as S
import Data.Sequence (Seq, (|>))
import GHC.TypeLits

-- | BitRange type.
data BitRange (w :: Nat) :: * where
  BitRange :: NatRepr w -- ^ width of range
           -> Int       -- ^ index of range start
           -> BitRange w

bitRange :: KnownNat w => Int -> BitRange w
bitRange start = BitRange knownNat start

instance Show (BitRange w) where
  show (BitRange wRepr start) =
    "[" ++ show start ++ "..." ++ show (start + width - 1) ++ "]"
    where width = fromIntegral (natValue wRepr)

instance ShowF BitRange where
  showF = show

-- | BitLayout type. t is the target width, s is the source width. s should always be
-- less than or equal to t.
data BitLayout (t :: Nat) (s :: Nat) :: * where
  BitLayout :: NatRepr t -> NatRepr s -> Seq (Some BitRange) -> BitLayout t s

instance Show (BitLayout t s) where
  show (BitLayout _ _ br) = show br

empty :: KnownNat t => BitLayout t 0
empty = BitLayout knownNat knownNat S.empty

-- | TODO: either here or at the end, do some kind of runtime check to ensure this is
-- sensible. Probably best to do it here. Might be an easy way to implement it using
-- a bit vector.
(>:>) :: BitRange r -> BitLayout t s -> BitLayout t (r + s)
br@(BitRange rRepr _rangeStart) >:> BitLayout tRepr sRepr bitRanges =
  BitLayout tRepr (rRepr `addNat` sRepr) (bitRanges |> Some br)



-- TODO: check this
infixl 6 >:>
