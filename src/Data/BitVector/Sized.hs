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

This module should be imported qualified, as many of the names clash
with those in Prelude or other base packages.
-}

module Data.BitVector.Sized
  ( -- * 'BV.BV' type
    BV.BV, pattern BV
    -- * 'NatRepr's (from parameterized-utils)
  , NatRepr
  , knownNat
    -- * Constructors
  , mkBV, mkBVUnsafeUnsigned, mkBVUnsafeSigned
  , unsignedClamp, signedClamp
  , word8, word16, word32, word64
  , minUnsigned, maxUnsigned
  , minSigned, maxSigned
    -- * Conversions to Integer and Natural
  , asSigned
  , asUnsigned
  , asNatural
    -- * Bits operations (width-preserving)
    -- | 'BV' versions of the functions in @Data.Bits@.
  , and, or, xor
  , complement
  , shl, lshr, ashr, rotateL, rotateR
  , zero, one, width
  , bit, bit'
  , setBit, setBit'
  , clearBit, clearBit'
  , complementBit, complementBit'
  , testBit, testBit'
  , popCount
  , ctz, clz
  , truncBits
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
  , select, select'
  , zext
  , sext
  , trunc, trunc'
  , mulWide
    -- * Enum operations
  , succUnsigned, succSigned
  , predUnsigned, predSigned
  , enumFromToUnsigned, enumFromToSigned
    -- * Pretty printing
  , ppHex
  , ppBin
  , ppOct
  , ppDec
  ) where

import Data.BitVector.Sized.Internal hiding (BV(..))
import qualified Data.BitVector.Sized.Internal as BV

import Data.Parameterized.NatRepr (knownNat, NatRepr)
import Prelude (Integer)

-- | Get the underlying 'Integer' representation from a 'BV'. Useful
-- for pattern matching against constants.
pattern BV :: Integer -> BV.BV w
pattern BV x <- BV.BV x
{-# COMPLETE BV #-}
