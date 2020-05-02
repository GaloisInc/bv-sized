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
with overflow flags. We only provide definitions for operators that
might actually overflow.

-}

module Data.BitVector.Sized.Overflow
  ( Overflow
  , overflowUnsigned
  , overflowSigned
  , result
  -- * Overflowing arithmetic operators
  , addOf
  , subOf
  , mulOf
  , squotOf
  , sremOf
  , sdivOf
  , smodOf
  ) where

import Data.Parameterized ( NatRepr )
import qualified Data.Parameterized.NatRepr as P

import Data.BitVector.Sized.Internal (BV(..), mkBV', asUnsigned, asSigned)

data UnsignedOverflow = UnsignedOverflow
                      | NoUnsignedOverflow
  deriving (Show, Eq)

instance Semigroup UnsignedOverflow where
  NoUnsignedOverflow <> NoUnsignedOverflow = NoUnsignedOverflow
  _ <> _ = UnsignedOverflow

instance Monoid UnsignedOverflow where
  mempty = NoUnsignedOverflow

data SignedOverflow = SignedOverflow
                    | NoSignedOverflow
  deriving (Show, Eq)

instance Semigroup SignedOverflow where
  NoSignedOverflow <> NoSignedOverflow = NoSignedOverflow
  _ <> _ = SignedOverflow

instance Monoid SignedOverflow where
  mempty = NoSignedOverflow

-- | A value annotated with overflow information.
data Overflow a =
  Overflow UnsignedOverflow SignedOverflow a
  deriving (Show, Eq)

-- | Return 'True' if a computation caused unsigned overflow.
overflowUnsigned :: Overflow a -> Bool
overflowUnsigned (Overflow UnsignedOverflow _ _) = True
overflowUnsigned _ = False

-- | Return 'True' if a computation caused signed overflow.
overflowSigned :: Overflow a -> Bool
overflowSigned (Overflow _ SignedOverflow _) = True
overflowSigned _ = False

-- | Return the result of a computation.
result :: Overflow a -> a
result (Overflow _ _ res) = res

instance Functor Overflow where
  fmap f (Overflow uof sof a) = Overflow uof sof (f a)

instance Applicative Overflow where
  pure a = Overflow mempty mempty a
  Overflow uof sof f <*> Overflow uof' sof' a =
    Overflow (uof <> uof') (sof <> sof') (f a)

-- | Monad for bitvector operations which might produce signed or
-- unsigned overflow.
instance Monad Overflow where
  Overflow uof sof a >>= k =
    let Overflow uof' sof' b = k a
    in Overflow (uof <> uof') (sof <> sof') b

-- | This only works if the operation has equivalent signed and
-- unsigned interpretations on bitvectors.
liftBinary :: (Integer -> Integer -> Integer)
           -> NatRepr w
           -> BV w -> BV w -> Overflow (BV w)
liftBinary op w xv yv =
  let ux = asUnsigned xv
      uy = asUnsigned yv
      sx = asSigned w xv
      sy = asSigned w yv

      ures = ux `op` uy
      sres = sx `op` sy

      uof = if ures < P.minUnsigned w || ures > P.maxUnsigned w
            then UnsignedOverflow
            else NoUnsignedOverflow
      sof = case P.isZeroOrGT1 w of
        Left P.Refl -> NoSignedOverflow
        Right P.LeqProof ->
          if sres < P.minSigned w || sres > P.maxSigned w
          then SignedOverflow
          else NoSignedOverflow
  in Overflow uof sof (mkBV' w ures)

-- | Bitvector add.
addOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
addOf = liftBinary (+)

-- | Bitvector subtract.
subOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
subOf = liftBinary (-)

-- | Bitvector multiply.
mulOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
mulOf = liftBinary (*)

-- | Bitvector division (signed). Rounds to zero. Division by zero
-- yields a runtime error.
squotOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
squotOf w bv1 bv2 = Overflow NoUnsignedOverflow sof (mkBV' w (x `quot` y))
  where x = asSigned w bv1
        y = asSigned w bv2
        sof = case P.isZeroOrGT1 w of
          Left P.Refl -> NoSignedOverflow
          Right P.LeqProof -> if (x == P.minSigned w && y == -1)
                              then SignedOverflow
                              else NoSignedOverflow

-- | Bitvector remainder after division (signed), when rounded to
-- zero. Division by zero yields a runtime error.
sremOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
sremOf w bv1 bv2 = Overflow NoUnsignedOverflow sof (mkBV' w (x `rem` y))
  where x = asSigned w bv1
        y = asSigned w bv2
        sof = case P.isZeroOrGT1 w of
          Left P.Refl -> NoSignedOverflow
          Right P.LeqProof -> if (x == P.minSigned w && y == -1)
                              then SignedOverflow
                              else NoSignedOverflow

-- | Bitvector division (signed). Rounds to zero. Division by zero
-- yields a runtime error.
sdivOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
sdivOf w bv1 bv2 = Overflow NoUnsignedOverflow sof (mkBV' w (x `div` y))
  where x = asSigned w bv1
        y = asSigned w bv2
        sof = case P.isZeroOrGT1 w of
          Left P.Refl -> NoSignedOverflow
          Right P.LeqProof -> if (x == P.minSigned w && y == -1)
                              then SignedOverflow
                              else NoSignedOverflow

-- | Bitvector remainder after division (signed), when rounded to
-- zero. Division by zero yields a runtime error.
smodOf :: NatRepr w -> BV w -> BV w -> Overflow (BV w)
smodOf w bv1 bv2 = Overflow NoUnsignedOverflow sof (mkBV' w (x `mod` y))
  where x = asSigned w bv1
        y = asSigned w bv2
        sof = case P.isZeroOrGT1 w of
          Left P.Refl -> NoSignedOverflow
          Right P.LeqProof -> if (x == P.minSigned w && y == -1)
                              then SignedOverflow
                              else NoSignedOverflow
