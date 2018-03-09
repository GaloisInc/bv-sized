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

module Data.BitVector.Sized.BitLayout
  ( ChunkIdx(..)
  , chunkIdx
  , BitLayout, empty, (|>)
  , inject
  , extract
  ) where

import Data.BitVector.Sized.Internal
import Data.Foldable
import Data.Parameterized
import qualified Data.Sequence as S
import Data.Sequence (Seq)
import GHC.TypeLits

-- | ChunkIdx type.
data ChunkIdx (w :: Nat) :: * where
  ChunkIdx :: NatRepr w -- width of range
           -> Int       -- index of range start
           -> ChunkIdx w

-- | Construct a ChunkIdx in a context where the chunk width is known at compile time.
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
  show (BitLayout _ _ cIdxs) = show cIdxs

-- | Construct an empty BitLayout.
empty :: KnownNat t => BitLayout t 0
empty = BitLayout knownNat knownNat S.empty

-- TODO: Should this be in Maybe?
-- | Add a chunk index to a bit layout.
(|>) :: ChunkIdx r -> BitLayout t s -> BitLayout t (r + s)
cIdx@(ChunkIdx rRepr _rangeStart) |> bl@(BitLayout tRepr sRepr chunkIdxs) =
  if cIdx `chunkFits` bl
  then BitLayout tRepr (rRepr `addNat` sRepr) (chunkIdxs S.|> Some cIdx)
  else error $ "chunk " ++ show cIdx ++ " does not fit in layout: " ++ show bl

-- TODO: check this
infixr 6 |>

chunkFits :: ChunkIdx r -> BitLayout t s -> Bool
chunkFits cIdx@(ChunkIdx rRepr _) (BitLayout tRepr sRepr chunkIdxs) =
  (natValue rRepr + natValue sRepr <= natValue tRepr) &&
  noOverlaps cIdx (toList chunkIdxs)

-- TODO: complete this function
noOverlaps :: ChunkIdx r -> [Some ChunkIdx] -> Bool
noOverlaps _cIdx _cIdxs = True

-- | Given a starting position, OR a smaller BitVector s with a larger BitVector t at
-- that position.
bvOrAt :: Int
       -> BitVector s
       -> BitVector t
       -> BitVector t
bvOrAt start sVec tVec@(BV tRepr _) =
  (bvZextWithRepr tRepr sVec `bvShift` start) `bvOr` tVec

-- | Given a list of ChunkIdxs, inject each chunk from a source BitVector s into a
-- target BitVector t.
bvOrAtAll :: NatRepr t
          -> [Some ChunkIdx]
          -> BitVector s
          -> BitVector t
bvOrAtAll tRepr [] _ = BV tRepr 0
bvOrAtAll tRepr (Some (ChunkIdx chunkRepr chunkStart) : chunkIdxs) sVec =
  bvOrAt chunkStart (bvTruncBits sVec chunkWidth) (bvOrAtAll tRepr chunkIdxs (sVec `bvShift` (- chunkWidth)))
  where chunkWidth = fromIntegral (natValue chunkRepr)

-- | Use a BitLayout to inject a smaller vector into a larger one.
inject :: BitLayout t s -> BitVector s -> BitVector t -> BitVector t
inject (BitLayout tRepr _ chunkIdxs) sVec tVec =
  (bvOrAtAll tRepr (toList chunkIdxs) sVec) `bvOr` tVec

-- First, extract the appropriate bits as a BitVector t, where the relevant bits
-- start at the LSB of the vector (so, mask and shiftL). Then, truncate to a
-- BitVector s, and shiftinto the starting position.
extractChunk :: NatRepr s     -- ^ width of output
             -> Int           -- ^ where to place the chunk in the result
             -> Some ChunkIdx -- ^ location/width of chunk in the input
             -> BitVector t   -- ^ input vector
             -> BitVector s
extractChunk sRepr sStart (Some (ChunkIdx chunkRepr tStart)) tVec =
  bvShift extractedChunk sStart
  where extractedChunk = bvZextWithRepr sRepr (bvExtractWithRepr chunkRepr tStart tVec)

extractAll :: NatRepr s       -- ^ determines width of output vector
           -> Int             -- ^ current position in output vector
           -> [Some ChunkIdx] -- ^ list of remaining chunks to place in output vector
           -> BitVector t     -- ^ input vector
           -> BitVector s
extractAll sRepr _ [] _ = BV sRepr 0
extractAll sRepr start (cIdx@(Some (ChunkIdx chunkRepr _)) : chunkIdxs) tVec =
  extractChunk sRepr start cIdx tVec `bvOr` extractAll sRepr (start + chunkWidth) chunkIdxs tVec
  where chunkWidth = fromInteger (natValue chunkRepr)

-- | Use a BitLayout to extract a smaller vector from a larger one.
extract :: BitLayout t s -> BitVector t -> BitVector s
extract (BitLayout _ sRepr chunkIdxs) tVec =
  extractAll sRepr 0 (toList chunkIdxs) tVec
