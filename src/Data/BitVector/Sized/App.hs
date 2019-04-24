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
  , bvAppWidth
  -- * Smart constructors
  , BVExpr(..)
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
  , eqE, (.==)
  , ltuE
  , ltsE
  -- ** Width-changing
  , zextE, zextE'
  , sextE, sextE'
  , extractE, extractE'
  , concatE
  -- ** Control
  , iteE
  ) where

import Control.Monad.Identity
import Data.BitVector.Sized
import Data.Parameterized
import Data.Parameterized.TH.GADT
import Foreign.Marshal.Utils (fromBool)
import GHC.TypeLits

-- | Represents the application of a 'BitVector' operation to one or more
-- subexpressions.
data BVApp (expr :: Nat -> *) (w :: Nat) where

  -- Bitwise operations
  AndApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  OrApp  :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  XorApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  NotApp :: !(NatRepr w) -> !(expr w) -> BVApp expr w

  -- Shifts
  SllApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  SrlApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  SraApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w

  -- Arithmetic operations
  AddApp   :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  SubApp   :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  MulApp   :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  QuotUApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  QuotSApp :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  RemUApp  :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  RemSApp  :: !(NatRepr w) -> !(expr w) -> !(expr w) -> BVApp expr w
  NegateApp :: !(NatRepr w) -> !(expr w) -> BVApp expr w
  AbsApp   :: !(NatRepr w) -> !(expr w) -> BVApp expr w
  SignumApp :: !(NatRepr w) -> !(expr w) -> BVApp expr w

  -- Comparisons
  EqApp  :: !(expr w) -> !(expr w) -> BVApp expr 1
  LtuApp :: !(expr w) -> !(expr w) -> BVApp expr 1
  LtsApp :: !(expr w) -> !(expr w) -> BVApp expr 1

  -- Width-changing
  ZExtApp    :: NatRepr w' -> !(expr w) -> BVApp expr w'
  SExtApp    :: NatRepr w' -> !(expr w) -> BVApp expr w'
  ExtractApp :: NatRepr w' -> NatRepr ix -> !(expr w) -> BVApp expr w'
  ConcatApp  :: !(NatRepr (w+w')) -> !(expr w) -> !(expr w') -> BVApp expr (w+w')

  -- Other operations
  IteApp :: !(NatRepr w) -> !(expr 1) -> !(expr w) -> !(expr w) -> BVApp expr w

bvAppWidth :: BVApp expr w -> NatRepr w
bvAppWidth (AndApp wRepr _ _) = wRepr
bvAppWidth (OrApp wRepr _ _) = wRepr
bvAppWidth (XorApp wRepr _ _) = wRepr
bvAppWidth (NotApp wRepr _) = wRepr

bvAppWidth (SllApp wRepr _ _) = wRepr
bvAppWidth (SrlApp wRepr _ _) = wRepr
bvAppWidth (SraApp wRepr _ _) = wRepr

bvAppWidth (AddApp wRepr _ _) = wRepr
bvAppWidth (SubApp wRepr _ _) = wRepr
bvAppWidth (MulApp wRepr _ _) = wRepr
bvAppWidth (QuotUApp wRepr _ _) = wRepr
bvAppWidth (QuotSApp wRepr _ _) = wRepr
bvAppWidth (RemUApp wRepr _ _) = wRepr
bvAppWidth (RemSApp wRepr _ _) = wRepr
bvAppWidth (NegateApp wRepr _) = wRepr
bvAppWidth (AbsApp wRepr _) = wRepr
bvAppWidth (SignumApp wRepr _) = wRepr

bvAppWidth (EqApp _ _) = knownNat
bvAppWidth (LtuApp _ _) = knownNat
bvAppWidth (LtsApp _ _) = knownNat

bvAppWidth (ZExtApp wRepr _) = wRepr
bvAppWidth (SExtApp wRepr _) = wRepr
bvAppWidth (ExtractApp wRepr _ _) = wRepr
bvAppWidth (ConcatApp wRepr _ _) = wRepr

bvAppWidth (IteApp wRepr _ _ _) = wRepr

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
evalBVAppM eval (AndApp _ e1 e2) = bvAnd <$> eval e1 <*> eval e2
evalBVAppM eval (OrApp  _ e1 e2) = bvOr  <$> eval e1 <*> eval e2
evalBVAppM eval (XorApp _ e1 e2) = bvXor <$> eval e1 <*> eval e2
evalBVAppM eval (NotApp _ e)     = bvComplement <$> eval e
evalBVAppM eval (AddApp _ e1 e2) = bvAdd <$> eval e1 <*> eval e2
evalBVAppM eval (SubApp _ e1 e2) = bvAdd <$> eval e1 <*> (bvNegate <$> eval e2)
evalBVAppM eval (SllApp _ e1 e2) = bvShiftL  <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (SrlApp _ e1 e2) = bvShiftRL <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (SraApp _ e1 e2) = bvShiftRA <$> eval e1 <*> (fromIntegral . bvIntegerU <$> eval e2)
evalBVAppM eval (MulApp _ e1 e2) = bvMul <$> eval e1 <*> eval e2
evalBVAppM eval (QuotSApp _ e1 e2) = bvQuotS  <$> eval e1 <*> eval e2
evalBVAppM eval (QuotUApp _ e1 e2) = bvQuotU  <$> eval e1 <*> eval e2
evalBVAppM eval (RemSApp  _ e1 e2) = bvRemS   <$> eval e1 <*> eval e2
evalBVAppM eval (RemUApp  _ e1 e2) = bvRemU   <$> eval e1 <*> eval e2
evalBVAppM eval (NegateApp _ e) = bvNegate <$> eval e
evalBVAppM eval (AbsApp _ e) = bvAbs <$> eval e
evalBVAppM eval (SignumApp _ e) = bvSignum <$> eval e
evalBVAppM eval (EqApp  e1 e2) = fromBool <$> ((==)  <$> eval e1 <*> eval e2)
evalBVAppM eval (LtuApp e1 e2) = fromBool <$> (bvLTU <$> eval e1 <*> eval e2)
evalBVAppM eval (LtsApp e1 e2) = fromBool <$> (bvLTS <$> eval e1 <*> eval e2)
evalBVAppM eval (ZExtApp wRepr e) = bvZext' wRepr <$> eval e
evalBVAppM eval (SExtApp wRepr e) = bvSext' wRepr <$> eval e
evalBVAppM eval (ExtractApp wRepr ixRepr e) =
  bvExtract' wRepr (fromIntegral $ intValue ixRepr) <$> eval e
evalBVAppM eval (ConcatApp _ e1 e2) = do
  e1Val <- eval e1
  e2Val <- eval e2
  return $ e1Val `bvConcat` e2Val
evalBVAppM eval (IteApp _ eTest eT eF) = do
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
  litBV :: BitVector w -> expr w
  exprWidth :: expr w -> NatRepr w
  appExpr :: BVApp expr w -> expr w

-- | Bitwise and.
andE :: BVExpr expr => expr w -> expr w -> expr w
andE e1 e2 = appExpr (AndApp (exprWidth e1) e1 e2)

-- | Bitwise or.
orE :: BVExpr expr => expr w -> expr w -> expr w
orE e1 e2 = appExpr (OrApp (exprWidth e1) e1 e2)

-- | Bitwise xor.
xorE :: BVExpr expr => expr w -> expr w -> expr w
xorE e1 e2 = appExpr (XorApp (exprWidth e1) e1 e2)

-- | Bitwise not.
notE :: BVExpr expr => expr w -> expr w
notE e = appExpr (NotApp (exprWidth e) e)

-- | Add two expressions.
addE :: BVExpr expr => expr w -> expr w -> expr w
addE e1 e2 = appExpr (AddApp (exprWidth e1) e1 e2)

-- | Subtract the second expression from the first.
subE :: BVExpr expr => expr w -> expr w -> expr w
subE e1 e2 = appExpr (SubApp (exprWidth e1) e1 e2)

-- | Signed multiply two 'BitVector's, doubling the width of the result to hold all
-- arithmetic overflow bits.
mulE :: BVExpr expr => expr w -> expr w -> expr w
mulE e1 e2 = appExpr (MulApp (exprWidth e1) e1 e2)

-- | Signed divide two 'BitVector's, rounding to zero.
quotsE :: BVExpr expr => expr w -> expr w -> expr w
quotsE e1 e2 = appExpr (QuotSApp (exprWidth e1) e1 e2)

-- | Unsigned divide two 'BitVector's, rounding to zero.
quotuE :: BVExpr expr => expr w -> expr w -> expr w
quotuE e1 e2 = appExpr (QuotUApp (exprWidth e1) e1 e2)

-- | Remainder after signed division of two 'BitVector's, when rounded to zero.
remsE :: BVExpr expr => expr w -> expr w -> expr w
remsE e1 e2 = appExpr (RemSApp (exprWidth e1) e1 e2)

-- | Remainder after unsigned division of two 'BitVector's, when rounded to zero.
remuE :: BVExpr expr => expr w -> expr w -> expr w
remuE e1 e2 = appExpr (RemUApp (exprWidth e1) e1 e2)

negateE :: BVExpr expr => expr w -> expr w
negateE e = appExpr (NegateApp (exprWidth e) e)

absE :: BVExpr expr => expr w -> expr w
absE e = appExpr (AbsApp (exprWidth e) e)

signumE :: BVExpr expr => expr w -> expr w
signumE e = appExpr (SignumApp (exprWidth e) e)

-- | Left logical shift the first expression by the second.
sllE :: BVExpr expr => expr w -> expr w -> expr w
sllE e1 e2 = appExpr (SllApp (exprWidth e1) e1 e2)

-- | Left logical shift the first expression by the second.
srlE :: BVExpr expr => expr w -> expr w -> expr w
srlE e1 e2 = appExpr (SrlApp (exprWidth e1) e1 e2)

-- | Left logical shift the first expression by the second.
sraE :: BVExpr expr => expr w -> expr w -> expr w
sraE e1 e2 = appExpr (SraApp (exprWidth e1) e1 e2)

-- | Test for equality of two expressions.
eqE :: BVExpr expr => expr w -> expr w -> expr 1
eqE e1 e2 = appExpr (EqApp e1 e2)

-- | Infix 'eqE'.
(.==) :: BVExpr expr => expr w -> expr w -> expr 1
(.==) = eqE

infix 4 .==

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
zextE' :: BVExpr expr => NatRepr w' -> expr w -> expr w'
zextE' repr e = appExpr (ZExtApp repr e)

-- | Sign-extension
sextE :: (BVExpr expr, KnownNat w') => expr w -> expr w'
sextE e = appExpr (SExtApp knownNat e)

-- | Sign-extension with an explicit width argument
sextE' :: BVExpr expr => NatRepr w' -> expr w -> expr w'
sextE' repr e = appExpr (SExtApp repr e)

-- | Extract bits
extractE :: (BVExpr expr, KnownNat w') => NatRepr ix -> expr w -> expr w'
extractE ixRepr e = appExpr (ExtractApp knownNat ixRepr e)

-- | Extract bits with an explicit width argument
extractE' :: BVExpr expr => NatRepr w' -> NatRepr ix -> expr w -> expr w'
extractE' wRepr ixRepr e = appExpr (ExtractApp wRepr ixRepr e)

-- | Concatenation
concatE :: BVExpr expr => expr w -> expr w' -> expr (w+w')
concatE e1 e2 = appExpr (ConcatApp (exprWidth e1 `addNat` exprWidth e2) e1 e2)

-- | Conditional branch.
iteE :: BVExpr expr => expr 1 -> expr w -> expr w -> expr w
iteE t e1 e2 = appExpr (IteApp (exprWidth e1) t e1 e2)
