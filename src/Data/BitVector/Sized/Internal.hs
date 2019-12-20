{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module defines a width-parameterized 'BV' type and various associated
operations that assume a 2's complement representation.
-}

module Data.BitVector.Sized.Internal where

import Data.Bits
-- import Data.Ix
import Data.Parameterized
import GHC.Generics
import GHC.TypeLits
-- import Numeric
-- import System.Random
-- import Test.QuickCheck (Arbitrary(..), choose)
-- import Text.PrettyPrint.HughesPJClass
-- import Text.Printf
-- import Unsafe.Coerce (unsafeCoerce)

----------------------------------------
-- BitVector data type definitions

-- | Bitvector datatype, parameterized by width.
data BV (w :: Nat) :: * where
  BV :: Integer -> BV w
  -- Q: We provide an Ord instance as an arbitrary ordering so that
  -- 'BV' can be stored in data structures requiring such.
  deriving (Generic, Show, Read, Eq, Ord)

instance ShowF BV

instance EqF BV where
  BV bv `eqF` BV bv' = bv == bv'

-- Q: We cannot implement TestEquality or OrdF.
-- instance TestEquality BitVector where
--   testEquality (BV x) (BV y) =
--     if natValue wRepr == natValue wRepr' && x == y
--     then Just (unsafeCoerce (Refl :: a :~: a))
--     else Nothing

-- instance OrdF BV where
--   BV x `compareF` BV y = fromOrdering (x `compare` y)
--     -- case xRepr `compareF` yRepr of
--     --   EQF -> fromOrdering (x `compare` y)
--     --   cmp -> cmp

-- -- | 'BV' can be treated as a constructor for pattern matching, but to build
-- -- one you must use `fromInteger`.
-- pattern BV :: NatRepr w -> Integer -> BV w
-- pattern BV wRepr x <- BV wRepr x
-- {-# COMPLETE BV #-}

-- | Construct a bit vector with a particular width, where the width is inferrable
-- from the type context. The input (an unbounded data type, hence with an
-- infinite-width bit representation), whether positive or negative, is silently
-- truncated to fit into the number of bits demanded by the return type.
--
-- >>> mkBV 0xA :: BV 4
-- 0xa
-- >>> mkBV 0xA :: BV 2
-- 0x2
mkBV :: KnownNat w => Integer -> BV w
mkBV x = mkBV' knownNat x

-- | Like 'bv', but with an explict 'NatRepr'.
mkBV' :: NatRepr w -> Integer -> BV w
mkBV' wRepr x = BV (truncBits width (fromIntegral x))
  where width = natValue wRepr

-- | The zero bitvector with width 0.
bv0 :: BV 0
bv0 = mkBV (0 :: Integer)

----------------------------------------
-- BitVector -> Integer functions

-- | Unsigned interpretation of a bit vector as a (positive) Integer.
bvIntegerU :: BV w -> Integer
bvIntegerU (BV x) = x

-- | Signed interpretation of a bit vector as an Integer.
bvIntegerS :: NatRepr w -> BV w -> Integer
bvIntegerS wRepr bv = if bvTestBit bv (width - 1)
                then bvIntegerU bv - (1 `shiftL` width)
                else bvIntegerU bv
  where width = fromIntegral (natValue wRepr)

----------------------------------------
-- BV w operations (fixed width)

-- | Bitwise and.
bvAnd :: BV w -> BV w -> BV w
bvAnd (BV x) (BV y) = BV (x .&. y)

-- | Bitwise or.
bvOr :: BV w -> BV w -> BV w
bvOr (BV x) (BV y) = BV (x .|. y)

-- | Bitwise xor.
bvXor :: BV w -> BV w -> BV w
bvXor (BV x) (BV y) = BV (x `xor` y)

-- | Bitwise complement (flip every bit).
bvComplement :: NatRepr w -> BV w -> BV w
bvComplement wRepr (BV x) = BV (truncBits width (complement x))
  where width = natValue wRepr

-- | Bitwise shift. Uses an arithmetic right shift.
bvShift :: NatRepr w -> BV w -> Int -> BV w
bvShift wRepr bv@(BV _) shf = BV (truncBits width (x `shift` shf))
  where width = natValue wRepr
        x     = bvIntegerS wRepr bv -- arithmetic right shift when negative

toPos :: Int -> Int
toPos x | x < 0 = 0
toPos x = x

-- | Left shift.
bvShiftL :: NatRepr w -> BV w -> Int -> BV w
bvShiftL wRepr bv shf = bvShift wRepr bv (toPos shf)

-- | Right arithmetic shift.
bvShiftRA :: NatRepr w -> BV w -> Int -> BV w
bvShiftRA wRepr bv shf = bvShift wRepr bv (- (toPos shf))

-- | Right logical shift.
bvShiftRL :: NatRepr w -> BV w -> Int -> BV w
bvShiftRL wRepr bv@(BV _) shf = BV (truncBits width (x `shift` (- toPos shf)))
  where width = natValue wRepr
        x     = bvIntegerU bv

-- | Bitwise rotate.
bvRotate :: NatRepr w -> BV w -> Int -> BV w
bvRotate wRepr bv rot' = leftChunk `bvOr` rightChunk
  where rot = rot' `mod` width
        leftChunk = bvShift wRepr bv rot
        rightChunk = bvShift wRepr bv (rot - width)
        width = fromIntegral (natValue wRepr)

-- Q: Is there a right way to implement this here?
-- -- | Get the width of a 'BV'.
-- bvWidth :: BV w -> Int
-- bvWidth (BV wRepr _) = fromIntegral (natValue wRepr)

-- | Test if a particular bit is set.
bvTestBit :: BV w -> Int -> Bool
bvTestBit (BV x) b = testBit x b

-- | Get the number of 1 bits in a 'BV'.
bvPopCount :: BV w -> Int
bvPopCount (BV x) = popCount x

-- | Truncate a bit vector to a particular width given at runtime, while keeping the
-- type-level width constant.
bvTruncBits :: BV w -> Int -> BV w
bvTruncBits (BV x) b = BV (truncBits b x)

----------------------------------------
-- BV w arithmetic operations (fixed width)

-- | Bitwise add.
bvAdd :: NatRepr w -> BV w -> BV w -> BV w
bvAdd wRepr (BV x) (BV y) = BV (truncBits width (x + y))
  where width = natValue wRepr

-- | Bitwise multiply.
bvMul :: NatRepr w -> BV w -> BV w -> BV w
bvMul wRepr (BV x) (BV y) = BV (truncBits width (x * y))
  where width = natValue wRepr

-- | Bitwise division (unsigned). Rounds to zero.
bvQuotU :: BV w -> BV w -> BV w
bvQuotU (BV x) (BV y) = BV (x `quot` y)

-- | Bitwise division (signed). Rounds to zero (not negative infinity).
bvQuotS :: NatRepr w -> BV w -> BV w -> BV w
bvQuotS wRepr bv1@(BV _) bv2 = BV (truncBits width (x `quot` y))
  where x = bvIntegerS wRepr bv1
        y = bvIntegerS wRepr bv2
        width = natValue wRepr

-- | Bitwise remainder after division (unsigned), when rounded to zero.
bvRemU :: BV w -> BV w -> BV w
bvRemU (BV x) (BV y) = BV (x `rem` y)

-- | Bitwise remainder after  division (signed), when rounded to zero (not negative
-- infinity).
bvRemS :: NatRepr w -> BV w -> BV w -> BV w
bvRemS wRepr bv1@(BV _) bv2 = BV (truncBits width (x `rem` y))
  where x = bvIntegerS wRepr bv1
        y = bvIntegerS wRepr bv2
        width = natValue wRepr

-- | Bitwise absolute value.
bvAbs :: NatRepr w -> BV w -> BV w
bvAbs wRepr bv@(BV _) = BV abs_x
  where width = natValue wRepr
        x     = bvIntegerS wRepr bv
        abs_x = truncBits width (abs x) -- this is necessary

-- | Bitwise negation.
bvNegate :: NatRepr w -> BV w -> BV w
bvNegate wRepr (BV x) = BV (truncBits width (-x))
  where width = fromIntegral (natValue wRepr) :: Integer

-- | Get the sign bit as a 'BV'.
bvSignum :: NatRepr w -> BV w -> BV w
bvSignum wRepr bv@(BV _) = bvShift wRepr bv (1 - width) `bvAnd` BV 0x1
  where width = fromIntegral (natValue wRepr)

-- | Signed less than.
bvLTS :: NatRepr w -> BV w -> BV w -> Bool
bvLTS wRepr bv1 bv2 = bvIntegerS wRepr bv1 < bvIntegerS wRepr bv2

-- | Unsigned less than.
bvLTU :: BV w -> BV w -> Bool
bvLTU bv1 bv2 = bvIntegerU bv1 < bvIntegerU bv2

----------------------------------------
-- Width-changing operations

-- -- | Concatenate two bit vectors.
-- --
-- -- >>> (0xAA :: BV 8) `bvConcat` (0xBCDEF0 :: BV 24)
-- -- 0xaabcdef0
-- -- >>> :type it
-- -- it :: BV 32
-- --
-- -- Note that the first argument gets placed in the higher-order bits. The above
-- -- example should be illustrative enough.
-- bvConcat :: BV v -> BV w -> BV (v+w)
-- bvConcat (BV hiWRepr hi) (BV loWRepr lo) =
--   BV (hiWRepr `addNat` loWRepr) ((hi `shiftL` loWidth) .|. lo)
--   where loWidth = fromIntegral (natValue loWRepr)

-- -- | Infix 'bvConcat'.
-- (<:>) :: BV v -> BV w -> BV (v+w)
-- (<:>) = bvConcat

-- bvConcatSome :: Some BV -> Some BV -> Some BV
-- bvConcatSome (Some bv1) (Some bv2) = Some (bv2 <:> bv1)

-- -- | Concatenate a list of 'BV's into a 'BV' of arbitrary width. The ordering is little endian:
-- --
-- -- >>> bvConcatMany [0xAA :: BV 8, 0xBB] :: BV 16
-- -- 0xbbaa
-- -- >>> bvConcatMany [0xAA :: BV 8, 0xBB, 0xCC] :: BV 16
-- -- 0xbbaa
-- --
-- -- If the sum of the widths of the input 'BV's exceeds the output width, we
-- -- ignore the tail end of the list.
-- bvConcatMany :: KnownNat w' => [BV w] -> BV w'
-- bvConcatMany = bvConcatMany' knownNat

-- -- | 'bvConcatMany' with an explicit 'NatRepr'.
-- bvConcatMany' :: NatRepr w' -> [BV w] -> BV w'
-- bvConcatMany' wRepr bvs =
--   viewSome (bvZext' wRepr) $ foldl bvConcatSome (Some bv0) (Some <$> bvs)

-- infixl 6 <:>

-- -- | Slice out a smaller bit vector from a larger one. The lowest significant bit is
-- -- given explicitly as an argument of type 'Int', and the length of the slice is
-- -- inferred from a type-level context.
-- --
-- -- >>> bvExtract 12 (0xAABCDEF0 :: BV 32) :: BV 8
-- -- 0xcd
-- --
-- -- Note that 'bvExtract' does not do any bounds checking whatsoever; if you try and
-- -- extract bits that aren't present in the input, you will get 0's.
-- bvExtract :: forall w w' . (KnownNat w')
--           => Int
--           -> BV w
--           -> BV w'
-- bvExtract pos bv = bv xShf
--   where (BV _ xShf) = bvShift bv (- pos)

-- -- | Unconstrained variant of 'bvExtract' with an explicit 'NatRepr' argument.
-- bvExtract' :: NatRepr w'
--                   -> Int
--                   -> BV w
--                   -> BV w'
-- bvExtract' repr pos bv = BV repr (truncBits width xShf)
--   where (BV _ xShf) = bvShift bv (- pos)
--         width = natValue repr

-- -- | Zero-extend a vector to one of greater length. If given an input of greater
-- -- length than the output type, this performs a truncation.
-- bvZext :: forall w w' . KnownNat w'
--        => BV w
--        -> BV w'
-- bvZext (BV _ x) = bv x

-- -- | Unconstrained variant of 'bvZext' with an explicit 'NatRepr' argument.
-- bvZext' :: NatRepr w'
--                -> BV w
--                -> BV w'
-- bvZext' repr (BV _ x) = BV repr (truncBits width x)
--   where width = natValue repr

-- -- | Sign-extend a vector to one of greater length. If given an input of greater
-- -- length than the output type, this performs a truncation.
-- bvSext :: forall w w' . KnownNat w'
--        => BV w
--        -> BV w'
-- bvSext bv = bv (bvIntegerS bv)

-- -- | Unconstrained variant of 'bvSext' with an explicit 'NatRepr' argument.
-- bvSext' :: NatRepr w'
--                -> BV w
--                -> BV w'
-- bvSext' repr bv = BV repr (truncBits width (bvIntegerS bv))
--   where width = natValue repr

----------------------------------------
-- Byte decomposition

-- -- | Given a 'BV' of arbitrary length, decompose it into a list of bytes. Uses
-- -- an unsigned interpretation of the input vector, so if you ask for more bytes that
-- -- the 'BV' contains, you get zeros. The result is little-endian, so the first
-- -- element of the list will be the least significant byte of the input vector.
-- bvGetBytesU :: Int -> BV w -> [BV 8]
-- bvGetBytesU n _ | n <= 0 = []
-- bvGetBytesU n bv = bvExtract 0 bv : bvGetBytesU (n-1) (bvShiftRL bv 8)

----------------------------------------
-- Bits

-- | Mask for a specified number of lower bits.
lowMask :: (Integral a, Bits b) => a -> b
lowMask numBits = complement (complement zeroBits `shiftL` fromIntegral numBits)

-- | Truncate to a specified number of lower bits.
truncBits :: (Integral a, Bits b) => a -> b -> b
truncBits width b = b .&. lowMask width

----------------------------------------
-- Class instances
--- $(return [])

-- instance OrdF BitVector where
--   (BV xRepr x) `compareF` (BV yRepr y) =
--     case xRepr `compareF` yRepr of
--       EQF -> fromOrdering (x `compare` y)
--       cmp -> cmp

-- instance TestEquality BitVector where
--   testEquality (BV wRepr x) (BV wRepr' y) =
--     if natValue wRepr == natValue wRepr' && x == y
--     then Just (unsafeCoerce (Refl :: a :~: a))
--     else Nothing

-- instance KnownNat w => Bits (BitVector w) where
--   (.&.)        = bvAnd
--   (.|.)        = bvOr
--   xor          = bvXor
--   complement   = bvComplement
--   shift        = bvShift
--   rotate       = bvRotate
--   bitSize      = bvWidth
--   bitSizeMaybe = Just . bvWidth
--   isSigned     = const False
--   testBit      = bvTestBit
--   bit          = bitVector . (bit :: Int -> Integer)
--   popCount     = bvPopCount

-- instance KnownNat w => FiniteBits (BitVector w) where
--   finiteBitSize = bvWidth

-- instance KnownNat w => Num (BitVector w) where
--   (+)         = bvAdd
--   (*)         = bvMul
--   abs         = bvAbs
--   signum      = bvSignum
--   fromInteger = bitVector
--   negate      = bvNegate

-- instance KnownNat w => Enum (BitVector w) where
--   toEnum   = bitVector . fromIntegral
--   fromEnum = fromIntegral . bvIntegerU

-- instance KnownNat w => Ix (BitVector w) where
--   range (lo, hi) = bitVector <$> [bvIntegerU lo .. bvIntegerU hi]
--   index (lo, hi) bv = index (bvIntegerU lo, bvIntegerU hi) (bvIntegerU bv)
--   inRange (lo, hi) bv = inRange (bvIntegerU lo, bvIntegerU hi) (bvIntegerU bv)

-- instance KnownNat w => Bounded (BitVector w) where
--   minBound = bitVector (0 :: Integer)
--   maxBound = bitVector ((-1) :: Integer)

-- instance KnownNat w => Arbitrary (BitVector w) where
--   arbitrary = choose (minBound, maxBound)

-- instance KnownNat w => Random (BitVector w) where
--   randomR (bvLo, bvHi) gen =
--     let (x, gen') = randomR (bvIntegerU bvLo, bvIntegerU bvHi) gen
--     in (bitVector x, gen')
--   random gen =
--     let (x :: Integer, gen') = random gen
--     in (bitVector x, gen')

-- prettyHex :: (Integral a, PrintfArg a, Show a) => a -> Integer -> String
-- prettyHex width val = printf format val width
--   where -- numDigits = (width+3) `quot` 4
--         -- format = "0x%." ++ show numDigits ++ "x<%d>"
--         format = "0x%x<%d>"

-- instance Pretty (BitVector w) where
--   -- | Pretty print a bit vector (shows its width)
--   pPrint (BV wRepr x) = text $ prettyHex (natValue wRepr) x
