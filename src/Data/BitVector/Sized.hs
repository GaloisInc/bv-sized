{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a width-parameterized 'BitVector' type and various associated
operations that assume a 2's complement representation.
-}

module Data.BitVector.Sized
  ( -- * 'BV' type
    BV
  , mkBV, mkBVFromInteger
  , bv0
    -- * Bitwise operations (width-preserving)
    -- | These are alternative versions of some of the 'Data.Bits' functions where we
    -- do not need to know the width at compile time. They are all width-preserving.
  , bvAnd, bvOr, bvXor
  , bvComplement
  , bvShift, bvShiftL, bvShiftRA, bvShiftRL, bvRotate
  , bvTestBit
  , bvPopCount
  , bvTruncBits
    -- * Arithmetic operations (width-preserving)
  , bvAdd, bvMul
  , bvQuotU, bvQuotS
  , bvRemU, bvRemS
  , bvAbs, bvNegate
  , bvSignum
  , bvLTS, bvLTU
  --   -- * Variable-width operations
  --   -- | These are functions that involve bit vectors of different lengths.
  , bvConcat
  , bvExtract
  , bvZext
  , bvSext
    -- * Conversions to Integer/Natural
  , bvInteger
  , bvNatural
    -- * parameterized-utils re-exports
  , NatRepr
  , knownNat
  --   -- * Byte decomposition
  -- , bvGetBytesU
  ) where

import Data.BitVector.Sized.Internal

import Data.Parameterized.NatRepr (knownNat, NatRepr)
