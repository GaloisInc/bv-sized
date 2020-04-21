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

All type class instances assume unsigned representations -- for the signed instances, see 'Data.BitVector.Sized.Signed'.
-}

module Data.BitVector.Sized
  ( -- * 'BV' type
    BV
    -- * Functions that create bitvectors
  , mkBV
  , zero, bit, bit'
  , minUnsigned, maxUnsigned
  , minSigned, maxSigned
  , unsignedClamp, signedClamp
    -- * Bitwise operations (width-preserving)
  , and, or, xor
  , complement
  , lshr, ashr, shl, rotateL, rotateR
  , testBit
  , popCount
  , truncBits
    -- * Arithmetic operations (width-preserving)
  , add, sub, mul
  , uquot, squot, sdiv
  , urem, srem, smod
  , abs, negate
  , signBit
  , slt, sle, ult, ule
  , umin, umax
    -- * Variable-width operations
    -- | These are functions that involve bit vectors of different lengths.
  , concat
  , extract
  , zext
  , sext
    -- * Conversions to signed/unsigned Integer
  , asSigned
  , asUnsigned
    -- * parameterized-utils re-exports
  , NatRepr
  , knownNat
  ) where

import Data.BitVector.Sized.Internal

import Data.Parameterized.NatRepr (knownNat, NatRepr)
import Prelude ()
