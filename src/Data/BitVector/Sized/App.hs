{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-|
Module      : Data.BitVector.Sized.App
Copyright   : (c) Benjamin Selfridge, 2018
                  Galois Inc.
License     : None (yet)
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
  ) where

import Control.Monad.Identity
import Data.BitVector.Sized
import Data.Parameterized
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
  MulSApp  :: !(expr w) -> !(expr w) -> BVApp expr (w+w)
  MulUApp  :: !(expr w) -> !(expr w) -> BVApp expr (w+w)
  MulSUApp :: !(expr w) -> !(expr w) -> BVApp expr (w+w)
  DivUApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  DivSApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  RemUApp  :: !(expr w) -> !(expr w) -> BVApp expr w
  RemSApp  :: !(expr w) -> !(expr w) -> BVApp expr w

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
evalBVAppM eval (MulSApp  e1 e2) = bvMulFS  <$> eval e1 <*> eval e2
evalBVAppM eval (MulUApp  e1 e2) = bvMulFU  <$> eval e1 <*> eval e2
evalBVAppM eval (MulSUApp e1 e2) = bvMulFSU <$> eval e1 <*> eval e2
evalBVAppM eval (DivSApp  e1 e2) = bvQuotS  <$> eval e1 <*> eval e2
evalBVAppM eval (DivUApp  e1 e2) = bvQuotU  <$> eval e1 <*> eval e2
evalBVAppM eval (RemSApp  e1 e2) = bvRemS   <$> eval e1 <*> eval e2
evalBVAppM eval (RemUApp  e1 e2) = bvRemU   <$> eval e1 <*> eval e2
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
  tVal <- eval eT
  fVal <- eval eF
  return $ if testVal == 1 then tVal else fVal

-- | Evaluate a 'BVApp' given a pure evaluation function for the parameterized type @expr@.
evalBVApp :: (forall w' . expr w' -> BitVector w') -- ^ expression evaluator
          -> BVApp expr w                          -- ^ application
          -> BitVector w
evalBVApp eval bvApp = runIdentity $ evalBVAppM (return . eval) bvApp
