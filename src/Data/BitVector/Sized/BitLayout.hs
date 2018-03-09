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

This module defines a 'BitLayout' datatype which encodes a chunk-to-chunk mapping (no
overlaps) from a smaller bit vector into a larger one.
-}

module Data.BitVector.Sized.BitLayout where

import Data.BitVector.Sized.Internal
import Data.Foldable
import Data.Parameterized
import qualified Data.Sequence as S
import Data.Sequence (Seq)
import GHC.TypeLits

-- | ChunkIdx type.
data ChunkIdx (w :: Nat) :: * where
  ChunkIdx :: NatRepr w -- ^ width of range
           -> Int       -- ^ index of range start
           -> ChunkIdx w

chunkIdx :: KnownNat w => Int -> ChunkIdx w
chunkIdx start = ChunkIdx knownNat start

instance Show (ChunkIdx w) where
  show (ChunkIdx wRepr start) =
    "[" ++ show start ++ "..." ++ show (start + width - 1) ++ "]"
    where width = fromIntegral (natValue wRepr)

instance ShowF ChunkIdx where
  showF = show

-- | BitLayout type. t is the target width, s is the source width. s should always be
-- less than or equal to t.
data BitLayout (t :: Nat) (s :: Nat) :: * where
  BitLayout :: NatRepr t -> NatRepr s -> Seq (Some ChunkIdx) -> BitLayout t s

instance Show (BitLayout t s) where
  show (BitLayout _ _ br) = show br

empty :: KnownNat t => BitLayout t 0
empty = BitLayout knownNat knownNat S.empty

-- TODO: either here or at the end, do some kind of runtime check to ensure this is
-- sensible. Probably best to do it here. Might be an easy way to implement it using
-- a bit vector.
singleton :: ChunkIdx r -> BitLayout r r
singleton br@(ChunkIdx repr _) = BitLayout repr repr (S.singleton $ Some br)

(|>) :: ChunkIdx r -> BitLayout t s -> BitLayout t (r + s)
br@(ChunkIdx rRepr _rangeStart) |> BitLayout tRepr sRepr chunkIdxs =
  BitLayout tRepr (rRepr `addNat` sRepr) (chunkIdxs S.|> Some br)

-- TODO: check this
infixl 6 |>

bvOrAt :: Int
       -> BitVector s
       -> BitVector t
       -> BitVector t
bvOrAt start sVec tVec@(BV tRepr _) =
  (bvZextWithRepr tRepr sVec `bvShift` start) `bvOr` tVec

-- TODO: runtime check, possibly throw runtime error.
bvOrAtAll :: NatRepr t
          -> [Some ChunkIdx]
          -> BitVector s
          -> BitVector t
bvOrAtAll tRepr [] _ = BV tRepr 0
bvOrAtAll tRepr (Some (ChunkIdx chunkRepr chunkStart) : chunkIdxs) sVec =
  bvOrAt chunkStart sVec (bvOrAtAll tRepr chunkIdxs (sVec `bvShift` (- chunkWidth)))
  where chunkWidth = fromIntegral (natValue chunkRepr)

inject :: BitLayout t s -> BitVector s -> BitVector t
inject (BitLayout tRepr _ chunkIdxs) sVec =
  bvOrAtAll tRepr (toList chunkIdxs) sVec

