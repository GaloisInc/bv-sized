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

This module defines a width-parameterized 'BV' type and various
associated operations. A @BV w@ is a newtype around an
'Prelude.Integer', so operations that require the width take an
explicit @NatRepr w@ argument. We omit all typeclass instances that
require compile-time knowledge of bitvector width, or force a signed
or unsigned intepretation. Those instances can be recovered via the
use of 'Data.BitVector.Sized.Signed.SignedBV' or
'Data.BitVector.Sized.Unsigned.UnsignedBV'.
-}

module Data.BitVector.Sized
  ( -- * 'BV' type
    BV
    -- * Functions that create bitvectors
  , mkBV, mkBVUnsafeUnsigned, mkBVUnsafeSigned
  , unsignedClamp, signedClamp
  , zero, one, width
  , bit, bit'
  , minUnsigned, maxUnsigned
  , minSigned, maxSigned
    -- * Bitwise operations (width-preserving)
  , and, or, xor
  , complement
  , lshr, ashr, shl, rotateL, rotateR
  , testBit
  , popCount
  , truncBits
    -- * Enum operations
  , succUnsigned, succSigned
  , predUnsigned, predSigned
  , enumFromToUnsigned, enumFromToSigned
    -- * Arithmetic operations (width-preserving)
  , add, sub, mul
  , uquot, squot, sdiv
  , urem, srem, smod
  , abs, negate
  , signBit
  , slt, sle, ult, ule
  , umin, umax
  , smin, smax
    -- * Variable-width operations
    -- | These are functions that involve bit vectors of different lengths.
  , concat
  , extract, extract'
  , zext
  , sext
  , trunc, trunc'
  , mulWide
    -- * Conversions to Integer and Natural
  , asSigned
  , asUnsigned
  , asNatural
    -- * parameterized-utils re-exports
  , NatRepr
  , knownNat
  ) where

import Data.BitVector.Sized.Internal

import Data.Parameterized.NatRepr (knownNat, NatRepr)
import Prelude ()
