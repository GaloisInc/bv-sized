{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
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
overlaps) from a smaller bit vector into a larger one. 'BitLayout's are especially
useful for defining the encoding and decoding of opcodes/operands in an instruction.
-}

module Data.BitVector.Sized.BitLayout
  ( -- * Chunk
    Chunk(..)
  , chunk
    -- * BitLayout
  , BitLayout
  , empty, (<:)
  , inject
  , extract
    -- * Lens
  , layoutLens
  ) where

import Data.BitVector.Sized
import Data.Foldable
import Control.Lens
import Data.Parameterized
import qualified Data.Sequence as S
import Data.Sequence (Seq)
import GHC.TypeLits

-- | 'Chunk' type, parameterized by chunk width. The internal 'Int' is the
-- position of the least significant bit of the chunk, and the type-level nat 'w' is
-- the width of the chunk.
--
-- >>> chunk 2 :: Chunk 5
-- [2...6]
--
-- Intuitively, the above chunk index captures the notion of /embedding/ a
-- 'BitVector' @5@ (bit vector of width 5) into a larger 'BitVector' at index 2,
-- preserving the order of the input bits. So an 5-bit input like @10011@ would map
-- to some larger bit vector containing the input starting at position 2, like
-- @000001001100@.
--
-- Multiple 'Chunk's comprise a 'BitLayout'; see below.
data Chunk (w :: Nat) :: * where
  Chunk :: NatRepr w -- width of range
        -> Int       -- index of range start
        -> Chunk w

-- | Construct a 'Chunk' in a context where the chunk width is known at compile time.
chunk :: KnownNat w => Int -> Chunk w
chunk start = Chunk knownNat start

instance Show (Chunk w) where
  show (Chunk wRepr start)
    | width > 0 =
      "[" ++ show (start + width - 1) ++ "..." ++ show start ++ "]"
    | otherwise = "[" ++ show start ++ "]"
    where width = fromIntegral (natValue wRepr)

instance ShowF Chunk where
  showF = show

-- | BitLayout type, parameterized by target width and source width. @t@ is the
-- target width, @s@ is the source width. @s@ should always be less than or equal to
-- @t@.
--
-- To construct a 'BitLayout', use the 'empty' constructor and the '|>' operator,
-- like so:
--
-- >>> empty :: BitLayout 32 0
-- []
-- >>> let layout = (chunk 25 :: Chunk 7) <: (chunk 7 :: Chunk 5) <: (empty :: BitLayout 32 0)
-- >>> layout
-- [[25...31],[7...11]]
-- >>> :type it
-- it :: BitLayout 32 12
--
-- In the above example @bitLayout@ defines a chunk-by-chunk mapping from a bit
-- vector of width 12 to one of width 32. We imagine the input vector of width 12
-- listed like so:
--
-- @
-- 0bMXXXXXXXXXXL
--   |-----||---|
--      7     5
-- @
--
-- Here, bit @M@ is the most significant bit, and @L@ is the least. The @BitLayout 32
-- 12@ defined above as the @layout@ variable would map that 12-bit vector to the
-- following 32-bit vector:
--
-- @
--      (Bit 25)          (Bit 5)
--         |                 |
--         |                 |
--         v                 v
-- 0bMXXXXXX0000000000000XXXXL0000000
--   |-----|             |---|
--      7                  5
-- @
--
-- To use a 'BitLayout' to achieve a bidirectional mapping like the one described
-- above, you can either use the 'Lens' interface or the functions 'inject' and
-- 'extract', which give an explicit setter and getter, respectively.
--
-- Example use of @inject@/@extract@:
--
-- >>> let bl = (chunk 25 :: Chunk 7) <: (chunk 7 :: Chunk 5) <: (empty :: BitLayout 32 0)
-- >>> bl
-- [[25...31],[7...11]]
-- >>> let sVec = bv 0b111111100001 :: BitVector 12
-- >>> sVec
-- 0xfe1<12>
-- >>> inject bl (bv 0) (bv 0b111111100001)
-- 0xfe000080<32>
-- >>> extract bl $ inject bl (bv 0) (bv 0b111111100001)
-- 0xfe1<12>

data BitLayout (t :: Nat) (s :: Nat) :: * where
  BitLayout :: NatRepr t -> NatRepr s -> Seq (Some Chunk) -> BitLayout t s

instance Show (BitLayout t s) where
  show (BitLayout _ _ cIdxs) = show (reverse $ toList cIdxs)

-- | Construct an empty 'BitLayout'.
empty :: KnownNat t => BitLayout t 0
empty = BitLayout knownNat knownNat S.empty

-- TODO: Should this be in Maybe?
-- | Add a 'Chunk' to a 'BitLayout'. If the 'Chunk' does not fit, either because the
-- resulting 'BitLayout' would be too long or because it would overlap with a 'Chunk'
-- that is already in the 'BitLayout', we throw an error.
(<:) :: Chunk r             -- ^ chunk to add
     -> BitLayout t s       -- ^ layout we are adding the chunk to
     -> BitLayout t (r + s)
cIdx@(Chunk rRepr _) <: bl@(BitLayout tRepr sRepr chunks) =
  if cIdx `chunkFits` bl
  then BitLayout tRepr (rRepr `addNat` sRepr) (chunks S.|> Some cIdx)
  else error $
       "chunk " ++ show cIdx ++ " does not fit in layout of size " ++
       show (natValue tRepr) ++ ": " ++ show bl

-- TODO: check precedence (associativity is correct)
infixr 6 <:

chunkFits :: Chunk r -> BitLayout t s -> Bool
chunkFits cIdx@(Chunk rRepr start) (BitLayout tRepr sRepr chunks) =
  (natValue rRepr + natValue sRepr <= natValue tRepr) && -- widths are ok
  (fromIntegral start + natValue rRepr <= natValue tRepr) && -- chunk lies within the bit vector
  (0 <= start) &&
  noOverlaps cIdx (toList chunks)

noOverlaps :: Chunk r -> [Some Chunk] -> Bool
noOverlaps cIdx cIdxs = all (chunksDontOverlap (Some cIdx)) cIdxs

chunksDontOverlap :: Some Chunk -> Some Chunk -> Bool
chunksDontOverlap (Some (Chunk chunkRepr1 start1)) (Some (Chunk chunkRepr2 start2)) =
  case start1 <= start2 of
    True  -> start1 + chunkWidth1 <= start2
    False -> start2 + chunkWidth2 <= start1
  where chunkWidth1 = fromIntegral (natValue chunkRepr1)
        chunkWidth2 = fromIntegral (natValue chunkRepr2)

-- | Given a starting position, insert (via "or") a smaller 'BitVector' @s@ with a larger
-- 'BitVector' @t@ at that position.
bvOrAt :: Int
       -> BitVector s
       -> BitVector t
       -> BitVector t
bvOrAt start sVec tVec@(BV tRepr _) =
  (bvZextWithRepr tRepr sVec `bvShift` start) `bvOr` tVec

-- | Given a list of 'Chunk's, inject each chunk from a source 'BitVector' @s@ into a
-- target 'BitVector' @t@.
bvOrAtAll :: NatRepr t
          -> [Some Chunk]
          -> BitVector s
          -> BitVector t
bvOrAtAll tRepr [] _ = BV tRepr 0
bvOrAtAll tRepr (Some (Chunk chunkRepr chunkStart) : chunks) sVec =
  bvOrAt chunkStart (bvTruncBits sVec chunkWidth) (bvOrAtAll tRepr chunks (sVec `bvShift` (- chunkWidth)))
  where chunkWidth = fromIntegral (natValue chunkRepr)

-- | Use a 'BitLayout' to inject a smaller vector into a larger one.
inject :: BitLayout t s -- ^ The layout
       -> BitVector t   -- ^ The larger vector to inject into
       -> BitVector s   -- ^ The smaller vector to be injected
       -> BitVector t
inject (BitLayout tRepr _ chunks) tVec sVec =
  (bvOrAtAll tRepr (toList chunks) sVec) `bvOr` tVec

-- First, extract the appropriate bits as a BitVector t, where the relevant bits
-- start at the LSB of the vector (so, mask and shiftL). Then, truncate to a
-- BitVector s, and shiftinto the starting position.
extractChunk :: NatRepr s     -- ^ width of output
             -> Int           -- ^ where to place the chunk in the result
             -> Some Chunk    -- ^ location/width of chunk in the input
             -> BitVector t   -- ^ input vector
             -> BitVector s
extractChunk sRepr sStart (Some (Chunk chunkRepr chunkStart)) tVec =
  bvShift extractedChunk sStart
  where extractedChunk = bvZextWithRepr sRepr (bvExtractWithRepr chunkRepr chunkStart tVec)

extractAll :: NatRepr s       -- ^ determines width of output vector
           -> Int             -- ^ current position in output vector
           -> [Some Chunk]    -- ^ list of remaining chunks to place in output vector
           -> BitVector t     -- ^ input vector
           -> BitVector s
extractAll sRepr _ [] _ = BV sRepr 0
extractAll sRepr outStart (cIdx@(Some (Chunk chunkRepr _)) : chunks) tVec =
  extractChunk sRepr outStart cIdx tVec `bvOr`
  extractAll sRepr (outStart + chunkWidth) chunks tVec
  where chunkWidth = fromInteger (natValue chunkRepr)

-- | Use a 'BitLayout' to extract a smaller vector from a larger one.
extract :: BitLayout t s -- ^ The layout
        -> BitVector t   -- ^ The larger vector to extract from
        -> BitVector s
extract (BitLayout _ sRepr chunks) tVec =
  extractAll sRepr 0 (toList chunks) tVec

-- | Lens for bit layout.
layoutLens :: BitLayout t s -> Simple Lens (BitVector t) (BitVector s)
layoutLens layout = lens (extract layout) (inject layout)
