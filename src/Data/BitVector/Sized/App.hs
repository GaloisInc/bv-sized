{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Data.BitVector.Sized.App
Copyright   : (c) Galois Inc. 2018
License     : BSD-3
Maintainer  : benselfridge@galois.com
Stability   : experimental
Portability : portable

This module exports a type, 'BVApp', to aid in building expression languages over
'BitVector's. Let @expr :: Nat -> *@ be some ADT of /expressions/ that yield
'BitVector's when evaluated. Then, given one or more values of type @expr w@
(i.e. one or more of these evaluatable expressions), 'BVApp' provides the various
constructors necessary for creating compound expressions involving pure 'BitVector'
operations. The @expr@ type can (and often will) include a constructor of type @BVApp
expr w -> expr w@ in order to create a recursive expression language.

In addition to the 'BVApp' type, we provide an evaluator which, given a function
mapping values of type @expr w@ to 'BitVector's, will evaluate the compound
'BVApp' expressions.
-}

module Data.BitVector.Sized.App
  ( BVApp(..)
  , evalBVApp
  , evalBVAppM
  -- * Smart constructors
  , BVExpr(..)
  , litBV
  -- ** Bitwise
  , andE
  , orE
  , xorE
  , notE
  -- ** Arithmetic
  , addE
  , subE
  , mulE
  , quotuE
  , quotsE
  , remuE
  , remsE
  , negateE
  , absE
  , signumE
  , sllE
  , srlE
  , sraE
  -- ** Comparison
  , eqE
  , ltuE
  , ltsE
  -- ** Width-changing
  , zextE, zextEWithRepr
  , sextE, sextEWithRepr
  , extractE, extractEWithRepr
  , concatE
  -- ** Control
  , iteE
  ) where

import Control.Monad.Identity
import Data.BitVector.Sized
import Data.Bits
import Data.Parameterized
import Data.Parameterized.TH.GADT
import Foreign.Marshal.Utils (fromBool)
import GHC.TypeLits

-- | Represents the application of a 'BitVector' operation to one or more
-- subexpressions.
data BVApp (expr :: Nat -> *) (w :: Nat) where
  -- Literal BitVector
  LitBVApp :: BitVector w -> BVApp expr w

  -- Bitwise operations
  AndApp :: !(expr w) -> !(expr w) -> BVApp expr w
  OrApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  XorApp :: !(expr w) -> !(expr w) -> BVApp expr w
  NotApp :: !(expr w) -> BVApp expr w

  -- Shifts
  SllApp :: !(expr w) -> !(expr w) -> BVApp expr w
  SrlApp :: !(expr w) -> !(expr w) -> BVApp expr w
  SraApp :: !(expr w) -> !(expr w) -> BVApp expr w

  -- Arithmetic operations
  AddApp   :: !(expr w) -> !(expr w) -> BVApp expr w
  SubApp   :: !(expr w) -> !(expr w) -> BVApp expr w
  MulApp   :: !(expr w) -> !(expr w) -> BVApp expr w
  QuotUApp :: !(expr w) -> !(expr w) -> BVApp expr w
  QuotSApp :: !(expr w) -> !(expr w) -> BVApp expr w
  RemUApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  RemSApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  NegateApp :: !(expr w) -> BVApp expr w
  AbsApp   :: !(expr w) -> BVApp expr w
  SignumApp :: !(expr w) -> BVApp expr w

  -- Comparisons
  EqApp  :: !(expr w) -> !(expr w) -> BVApp expr 1
  LtuApp :: !(expr w) -> !(expr w) -> BVApp expr 1
  LtsApp :: !(expr w) -> !(expr w) -> BVApp expr 1

  -- Width-changing
  ZExtApp    :: NatRepr w' -> !(expr w) -> BVApp expr w'
  SExtApp    :: NatRepr w' -> !(expr w) -> BVApp expr w'
  ExtractApp :: NatRepr w' -> Int -> !(expr w) -> BVApp expr w'
  ConcatApp  :: !(expr w) -> !(expr w') -> BVApp expr (w+w')

  -- Other operations
  IteApp :: !(expr 1) -> !(expr w) -> !(expr w) -> BVApp expr w

$(return [])

instance TestEquality expr => TestEquality (BVApp expr) where
  testEquality = $(structuralTypeEquality [t|BVApp|]
                   [ (AnyType `TypeApp` AnyType, [|testEquality|]) ])

instance TestEquality expr => Eq (BVApp expr w) where
  (==) = \x y -> isJust (testEquality x y)

instance TestEquality expr => EqF (BVApp expr) where
  eqF = (==)

instance OrdF expr => OrdF (BVApp expr) where
  compareF = $(structuralTypeOrd [t|BVApp|]
                [ (AnyType `TypeApp` AnyType, [|compareF|]) ])

instance OrdF expr => Ord (BVApp expr w) where
  compare a b =
    case compareF a b of
      LTF -> LT
      EQF -> EQ
      GTF -> GT

instance FunctorFC BVApp where
  fmapFC = fmapFCDefault

instance FoldableFC BVApp where
  foldMapFC = foldMapFCDefault

instance TraversableFC BVApp where
  traverseFC = $(structuralTraversal [t|BVApp|] [])

-- | Evaluate a 'BVApp' given a monadic evaluation function for the parameterized type @expr@.
evalBVAppM :: Monad m
           => (forall w' . expr w' -> m (BitVector w')) -- ^ expression evaluator
           -> BVApp expr w                              -- ^ application
           -> m (BitVector w)
evalBVAppM _ (LitBVApp bv) = return bv
evalBVAppM eval (AndApp e1 e2) = bvAnd <$> eval e1 <*> eval e2
evalBVAppM eval (OrApp  e1 e2) = bvOr  <$> eval e1 <*> eval e2
evalBVAppM eval (XorApp e1 e2) = bvXor <$> eval e1 <*> eval e2
evalBVAppM eval (NotApp e)     = bvComplement <$> eval e
evalBVAppM eval (AddApp e1 e2) = bvAdd <$> eval e1 <*> eval e2
evalBVAppM eval (SubApp e1 e2) = bvAdd <$> eval e1 <*> (bvNegate <$> eval e2)
evalBVAppM eval (SllApp e1 e2) = bvShiftL  <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (SrlApp e1 e2) = bvShiftRL <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (SraApp e1 e2) = bvShiftRA <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (MulApp e1 e2) = bvMul <$> eval e1 <*> eval e2
evalBVAppM eval (QuotSApp e1 e2) = bvQuotS  <$> eval e1 <*> eval e2
evalBVAppM eval (QuotUApp e1 e2) = bvQuotU  <$> eval e1 <*> eval e2
evalBVAppM eval (RemSApp  e1 e2) = bvRemS   <$> eval e1 <*> eval e2
evalBVAppM eval (RemUApp  e1 e2) = bvRemU   <$> eval e1 <*> eval e2
evalBVAppM eval (NegateApp e) = bvNegate <$> eval e
evalBVAppM eval (AbsApp e) = bvAbs <$> eval e
evalBVAppM eval (SignumApp e) = bvSignum <$> eval e
evalBVAppM eval (EqApp  e1 e2) = fromBool <$> ((==)  <$> eval e1 <*> eval e2)
evalBVAppM eval (LtuApp e1 e2) = fromBool <$> (bvLTU <$> eval e1 <*> eval e2)
evalBVAppM eval (LtsApp e1 e2) = fromBool <$> (bvLTS <$> eval e1 <*> eval e2)
evalBVAppM eval (ZExtApp wRepr e) = bvZextWithRepr wRepr <$> eval e
evalBVAppM eval (SExtApp wRepr e) = bvSextWithRepr wRepr <$> eval e
evalBVAppM eval (ExtractApp wRepr base e) = bvExtractWithRepr wRepr base <$> eval e
evalBVAppM eval (ConcatApp e1 e2) = do
  e1Val <- eval e1
  e2Val <- eval e2
  return $ e1Val `bvConcat` e2Val
evalBVAppM eval (IteApp eTest eT eF) = do
  testVal <- eval eTest
  case testVal of
    1 -> eval eT
    _ -> eval eF

-- | Evaluate a 'BVApp' given a pure evaluation function for the parameterized type @expr@.
evalBVApp :: (forall w' . expr w' -> BitVector w') -- ^ expression evaluator
          -> BVApp expr w                          -- ^ application
          -> BitVector w
evalBVApp eval bvApp = runIdentity $ evalBVAppM (return . eval) bvApp

-- | Typeclass for embedding 'BVApp' constructors into larger expression types.
class BVExpr (expr :: Nat -> *) where
  appExpr :: BVApp expr w -> expr w

instance (KnownNat w, BVExpr expr) => Num (BVApp expr w) where
  app1 + app2 = AddApp (appExpr app1) (appExpr app2)
  app1 * app2 = MulApp (appExpr app1) (appExpr app2)
  abs app = AbsApp (appExpr app)
  signum app = SignumApp (appExpr app)
  fromInteger x = LitBVApp (fromInteger x)
  negate app = NegateApp (appExpr app)
  app1 - app2 = SubApp (appExpr app1) (appExpr app2)

-- TODO: finish
instance (KnownNat w, BVExpr expr, TestEquality expr) => Bits (BVApp expr w) where
  app1 .&. app2 = AndApp (appExpr app1) (appExpr app2)
  app1 .|. app2 = OrApp (appExpr app1) (appExpr app2)
  app1 `xor` app2 = XorApp (appExpr app1) (appExpr app2)
  complement app = NotApp (appExpr app)
  shiftL app x = SllApp (appExpr app) (litBV (bitVector x))
  shiftR app x = SraApp (appExpr app) (litBV (bitVector x))
  rotate = undefined
  bitSize = undefined
  bitSizeMaybe = undefined
  isSigned = undefined
  testBit = undefined
  bit = undefined
  popCount = undefined

-- | Literal bit vector.
litBV :: BVExpr expr => BitVector w -> expr w
litBV = appExpr . LitBVApp

-- | Bitwise and.
andE :: BVExpr expr => expr w -> expr w -> expr w
andE e1 e2 = appExpr (AndApp e1 e2)

-- | Bitwise or.
orE :: BVExpr expr => expr w -> expr w -> expr w
orE e1 e2 = appExpr (OrApp e1 e2)

-- | Bitwise xor.
xorE :: BVExpr expr => expr w -> expr w -> expr w
xorE e1 e2 = appExpr (XorApp e1 e2)

-- | Bitwise not.
notE :: BVExpr expr => expr w -> expr w
notE e = appExpr (NotApp e)

-- | Add two expressions.
addE :: BVExpr expr => expr w -> expr w -> expr w
addE e1 e2 = appExpr (AddApp e1 e2)

-- | Subtract the second expression from the first.
subE :: BVExpr expr => expr w -> expr w -> expr w
subE e1 e2 = appExpr (SubApp e1 e2)

-- | Signed multiply two 'BitVector's, doubling the width of the result to hold all
-- arithmetic overflow bits.
mulE :: BVExpr expr => expr w -> expr w -> expr w
mulE e1 e2 = appExpr (MulApp e1 e2)

-- | Signed divide two 'BitVectors', rounding to zero.
quotsE :: BVExpr expr => expr w -> expr w -> expr w
quotsE e1 e2 = appExpr (QuotSApp e1 e2)

-- | Unsigned divide two 'BitVectors', rounding to zero.
quotuE :: BVExpr expr => expr w -> expr w -> expr w
quotuE e1 e2 = appExpr (QuotUApp e1 e2)

-- | Remainder after signed division of two 'BitVectors', when rounded to zero.
remsE :: BVExpr expr => expr w -> expr w -> expr w
remsE e1 e2 = appExpr (RemSApp e1 e2)

-- | Remainder after unsigned division of two 'BitVectors', when rounded to zero.
remuE :: BVExpr expr => expr w -> expr w -> expr w
remuE e1 e2 = appExpr (RemUApp e1 e2)

negateE :: BVExpr expr => expr w -> expr w
negateE e = appExpr (NegateApp e)

absE :: BVExpr expr => expr w -> expr w
absE e = appExpr (AbsApp e)

signumE :: BVExpr expr => expr w -> expr w
signumE e = appExpr (SignumApp e)

-- | Left logical shift the first expression by the second.
sllE :: BVExpr expr => expr w -> expr w -> expr w
sllE e1 e2 = appExpr (SllApp e1 e2)

-- | Left logical shift the first expression by the second.
srlE :: BVExpr expr => expr w -> expr w -> expr w
srlE e1 e2 = appExpr (SrlApp e1 e2)

-- | Left logical shift the first expression by the second.
sraE :: BVExpr expr => expr w -> expr w -> expr w
sraE e1 e2 = appExpr (SraApp e1 e2)

-- | Test for equality of two expressions.
eqE :: BVExpr expr => expr w -> expr w -> expr 1
eqE e1 e2 = appExpr (EqApp e1 e2)

-- | Signed less than
ltsE :: BVExpr expr => expr w -> expr w -> expr 1
ltsE e1 e2 = appExpr (LtsApp e1 e2)

-- | Unsigned less than
ltuE :: BVExpr expr => expr w -> expr w -> expr 1
ltuE e1 e2 = appExpr (LtuApp e1 e2)

-- | Zero-extension
zextE :: (BVExpr expr, KnownNat w') => expr w -> expr w'
zextE e = appExpr (ZExtApp knownNat e)

-- | Zero-extension with an explicit width argument
zextEWithRepr :: BVExpr expr => NatRepr w' -> expr w -> expr w'
zextEWithRepr repr e = appExpr (ZExtApp repr e)

-- | Sign-extension
sextE :: (BVExpr expr, KnownNat w') => expr w -> expr w'
sextE e = appExpr (SExtApp knownNat e)

-- | Sign-extension with an explicit width argument
sextEWithRepr :: BVExpr expr => NatRepr w' -> expr w -> expr w'
sextEWithRepr repr e = appExpr (SExtApp repr e)

-- | Extract bits
extractE :: (BVExpr expr, KnownNat w') => Int -> expr w -> expr w'
extractE base e = appExpr (ExtractApp knownNat base e)

-- | Extract bits with an explicit width argument
extractEWithRepr :: BVExpr expr => NatRepr w' -> Int -> expr w -> expr w'
extractEWithRepr wRepr base e = appExpr (ExtractApp wRepr base e)

-- | Concatenation
concatE :: BVExpr expr => expr w -> expr w' -> expr (w+w')
concatE e1 e2 = appExpr (ConcatApp e1 e2)

-- | Conditional branch.
iteE :: BVExpr expr => expr 1 -> expr w -> expr w -> expr w
iteE t e1 e2 = appExpr (IteApp t e1 e2)
