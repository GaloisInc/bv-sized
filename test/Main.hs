{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main where

-- Testing modules
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog

-- Modules under test
import qualified Data.BitVector.Sized as BV
import qualified Data.BitVector.Sized.Unsigned as BV
import qualified Data.BitVector.Sized.Signed as BV

-- Auxiliary modules
import Control.Monad.Random
import qualified Data.Bits as Bits
import qualified Data.ByteString as BS
import Data.Maybe (isJust, fromJust)
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.Pair
import Data.Word
import Numeric.Natural

----------------------------------------
-- Utilities
forcePos :: (1 <= w => NatRepr w -> a)
         -> NatRepr w -> a
forcePos f w = case isZeroOrGT1 w of
  Left Refl -> error "Main.forcePos: encountered 0 nat"
  Right LeqProof -> f w

----------------------------------------
-- Homomorphisms
un :: Show a
   => Gen (Some NatRepr)
   -- ^ generator for width
   -> (forall w . NatRepr w -> a -> BV.BV w)
   -- ^ morphism
   -> (forall w . NatRepr w -> Gen a)
   -- ^ generator for arg
   -> (forall w . NatRepr w -> a -> a)
   -- ^ unary operator on domain
   -> (forall w . NatRepr w -> BV.BV w -> BV.BV w)
   -- ^ unary operator on codomain
   -> Property
un genW p gen aOp bOp = property $ do
  Some w <- forAll genW
  a <- forAll (gen w)

  p w (aOp w a) === bOp w (p w a)

bin :: Show a
    => Gen (Some NatRepr)
    -- ^ generator for width
    -> (forall w. NatRepr w -> a -> BV.BV w)
    -- ^ morphism on domains
    -> (forall w. NatRepr w -> Gen a)
    -- ^ generator for first arg
    -> (forall w. NatRepr w -> Gen a)
    -- ^ generator for second arg
    -> (forall w. NatRepr w -> a -> a -> a)
    -- ^ binary operator on domain
    -> (forall w. NatRepr w -> BV.BV w -> BV.BV w -> BV.BV w)
    -- ^ binary operator on codomain
    -> Property
bin genW p gen1 gen2 aOp bOp = property $ do
  Some w <- forAll genW
  a1 <- forAll (gen1 w)
  a2 <- forAll (gen2 w)

  -- compute f (a1 `aOp` a2)
  let a1_a2  = aOp w a1 a2
  let pa1_a2 = p w a1_a2

  -- compute f (a1) `bOp` f (a2)
  let pa1     = p w a1
  let pa2     = p w a2
  let pa1_pa2 = bOp w pa1 pa2

  pa1_a2 === pa1_pa2

binPred :: Show a
        => Gen (Some NatRepr)
        -- ^ generator for width
        -> (forall w. NatRepr w -> a -> BV.BV w)
        -- ^ morphism on domains
        -> (forall w . NatRepr w -> Gen a)
        -- ^ generator for first arg
        -> (forall w . NatRepr w -> Gen a)
        -- ^ generator for second arg
        -> (forall w . NatRepr w -> a -> a -> Bool)
        -- ^ binary predicate on domain
        -> (forall w . NatRepr w -> BV.BV w -> BV.BV w -> Bool)
        -- ^ binary predicate on codomain
        -> Property
binPred genW p gen1 gen2 aPred bPred = property $ do
  Some w <- forAll genW
  a1 <- forAll (gen1 w)
  a2 <- forAll (gen2 w)

  let a1_a2  = aPred w a1 a2

  let pa1     = p w a1
  let pa2     = p w a2
  let pa1_pa2 = bPred w pa1 pa2

  a1_a2 === pa1_pa2

----------------------------------------
-- Ranges

anyWidth :: Gen (Some NatRepr)
anyWidth = mkNatRepr <$> (Gen.integral $ Range.linear 0 128)

byteWidth :: Gen (Some NatRepr)
byteWidth = mkNatRepr <$> (8*) <$> (Gen.integral $ Range.linear 0 16)

anyPosWidth :: Gen (Some NatRepr)
anyPosWidth = mkNatRepr <$> (Gen.integral $ Range.linear 1 128)

anyWidthGT1 :: Gen (Some NatRepr)
anyWidthGT1 = mkNatRepr <$> (Gen.integral $ Range.linear 2 128)

smallPosWidth :: Gen (Some NatRepr)
smallPosWidth = mkNatRepr <$> (Gen.integral $ Range.linear 1 4)

data NatReprLte w where
  NatReprLte :: (i <= w) => NatRepr i -> NatReprLte w

deriving instance Show (NatReprLte w)

natReprLte :: NatRepr w -> Gen (NatReprLte w)
natReprLte w = do
  n <- Gen.integral $ Range.linear 0 (natValue w)
  Some i <- return $ mkNatRepr n
  Just LeqProof <- return $ i `testLeq` w
  return $ NatReprLte i

data NatReprLt w where
  NatReprLt :: (i+1 <= w) => NatRepr i -> NatReprLt w

deriving instance Show (NatReprLt w)

natReprLt :: NatRepr w -> Gen (NatReprLt w)
natReprLt w = do
  n <- Gen.integral $ Range.linear 0 (natValue w - 1)
  Some i <- return $ mkNatRepr n
  NatCaseLT LeqProof <- return $ i `testNatCases` w
  return $ NatReprLt i

data NatReprPosLt w where
  NatReprPosLt :: (1 <= i, i+1 <= w) => NatRepr i -> NatReprPosLt w

deriving instance Show (NatReprPosLt w)

natReprPosLt :: NatRepr w -> Gen (NatReprPosLt w)
natReprPosLt w = do
  n <- Gen.integral $ Range.linear 1 (natValue w - 1)
  Some i <- return $ mkNatRepr n
  NatCaseLT LeqProof <- return $ i `testNatCases` w
  Right LeqProof <- return $ isZeroOrGT1 i
  return $ NatReprPosLt i

bytes :: Gen [Word8]
bytes = Gen.list (Range.linear 0 16) $ Gen.word8 Range.linearBounded

bits :: Gen [Bool]
bits = Gen.list (Range.linear 0 128) $ Gen.bool

unsigned :: NatRepr w -> Gen Integer
unsigned w = Gen.integral $ Range.linear 0 (maxUnsigned w)

unsignedPos :: NatRepr w -> Gen Integer
unsignedPos w = Gen.integral $ Range.linear 1 (maxUnsigned w)

largeUnsigned :: NatRepr w -> Gen Integer
largeUnsigned w = Gen.integral $ Range.linear 0 (maxUnsigned w')
  where w' = incNat w

signed :: NatRepr w -> Gen Integer
signed w = case isZeroOrGT1 w of
  Left Refl -> error "Main.signed: w = 0"
  Right LeqProof -> Gen.integral $ Range.linearFrom 0 (minSigned w) (maxSigned w)

signedPos :: NatRepr w -> Gen Integer
signedPos w = case isZeroOrGT1 w of
  Left Refl -> error "Main.posBounded: w = 0"
  Right LeqProof -> Gen.integral $ Range.linear 1 (maxSigned w)

signedNeg :: NatRepr w -> Gen Integer
signedNeg w = case isZeroOrGT1 w of
  Left Refl -> error "Main.posBounded: w = 0"
  Right LeqProof -> Gen.integral $ Range.linearFrom (-1) (minSigned w) (-1)

largeSigned :: NatRepr w -> Gen Integer
largeSigned w = Gen.integral $ Range.linearFrom 0 (- maxUnsigned w') (maxUnsigned w')
  where w' = incNat w

genPair :: Gen a -> Gen a -> Gen (a, a)
genPair gen gen' = do
  a <- gen
  a' <- gen'
  return (a, a')

----------------------------------------
-- Tests

bitwiseHomTests :: TestTree
bitwiseHomTests = testGroup "bitwise homomorphisms tests"
  [ testProperty "and" $ bin anyWidth BV.mkBV
    largeUnsigned largeUnsigned
    (const (Bits..&.)) (const BV.and)
  , testProperty "or" $ bin anyWidth BV.mkBV
    largeUnsigned largeUnsigned
    (const (Bits..|.)) (const BV.or)
  , testProperty "xor" $ bin anyWidth BV.mkBV
    largeUnsigned largeUnsigned
    (const Bits.xor) (const BV.xor)
  , testProperty "complement" $ un anyWidth BV.mkBV
    largeUnsigned
    (const Bits.complement) BV.complement
  ]

arithHomTests :: TestTree
arithHomTests = testGroup "arithmetic homomorphisms tests"
  [ testProperty "add" $ bin anyWidth BV.mkBV
    largeSigned largeSigned
    (const (+)) BV.add
  , testProperty "sub" $ bin anyWidth BV.mkBV
    largeSigned largeSigned
    (const (-)) BV.sub
  , testProperty "mul" $ bin anyWidth BV.mkBV
    largeSigned largeSigned
    (const (*)) BV.mul
  , testProperty "uquot" $ bin anyPosWidth BV.mkBV
    unsigned unsignedPos
    (const quot) (const BV.uquot)
  , testProperty "urem" $ bin anyPosWidth BV.mkBV
    unsigned unsignedPos
    (const rem) (const BV.urem)
  , testProperty "squot-pos-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedPos
    (const quot) (forcePos BV.squot)
  , testProperty "squot-neg-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedNeg
    (const quot) (forcePos BV.squot)
  , testProperty "srem-pos-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedPos
    (const rem) (forcePos BV.srem)
  , testProperty "srem-neg-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedNeg
    (const rem) (forcePos BV.srem)
  , testProperty "sdiv-pos-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedPos
    (const div) (forcePos BV.sdiv)
  , testProperty "sdiv-neg-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedNeg
    (const div) (forcePos BV.sdiv)
  , testProperty "smod-pos-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedPos
    (const mod) (forcePos BV.smod)
  , testProperty "smod-neg-denom" $ bin anyWidthGT1 BV.mkBV
    signed signedNeg
    (const mod) (forcePos BV.smod)
  , testProperty "abs" $ un anyPosWidth BV.mkBV
    signed
    (const abs) (forcePos BV.abs)
  , testProperty "negate" $ un anyPosWidth BV.mkBV
    largeSigned
    (const negate) BV.negate
  , testProperty "signBit" $ un anyPosWidth BV.mkBV
    signed
    (\_ a -> if a < 0 then 1 else 0) (forcePos BV.signBit)
  , testProperty "signum" $ un anyPosWidth BV.mkBV
    signed
    (\_ a -> signum a) (forcePos BV.signum)
  , testProperty "slt" $ binPred anyPosWidth BV.mkBV
    signed signed
    (const (<)) (forcePos BV.slt)
  , testProperty "sle" $ binPred anyPosWidth BV.mkBV
    signed signed
    (const (<=)) (forcePos BV.sle)
  , testProperty "ult" $ binPred anyWidth BV.mkBV
    unsigned unsigned
    (const (<)) (const BV.ult)
  , testProperty "ule" $ binPred anyWidth BV.mkBV
    unsigned unsigned
    (const (<=)) (const BV.ule)
  , testProperty "umin" $ bin anyWidth BV.mkBV
    unsigned unsigned
    (const min) (const BV.umin)
  , testProperty "umax" $ bin anyWidth BV.mkBV
    unsigned unsigned
    (const max) (const BV.umax)
  , testProperty "smin" $ bin anyPosWidth BV.mkBV
    signed signed
    (const min) (forcePos BV.smin)
  , testProperty "smax" $ bin anyPosWidth BV.mkBV
    signed signed
    (const max) (forcePos BV.smax)
  ]

serdeTest :: Gen (Some NatRepr)
          -> (forall w . NatRepr w -> BV.BV w -> Maybe a)
          -> (a -> Pair NatRepr BV.BV)
          -> Property
serdeTest wGen ser de = property $ do
  Some w <- forAll wGen
  i <- forAll (largeUnsigned w)
  let bv = BV.mkBV w i

  let a = ser w bv
  assert (isJust a)
  Pair w' bv' <- return $ de $ fromJust a

  assert (isJust (w' `testEquality` w))
  Just Refl <- return $ w' `testEquality` w
  bv' === bv

deserTest :: (Show a, Eq a)
          => Gen a
          -> (a -> Int)
          -> (a -> Pair NatRepr BV.BV)
          -> (forall w . NatRepr w -> BV.BV w -> Maybe a)
          -> Property
deserTest genA lenA de ser = property $ do
  a <- forAll genA
  Some w' <- return $ mkNatRepr (fromIntegral (lenA a))

  Pair w bv <- return $ de $ a

  assert (isJust (w' `testEquality` w))
  Just Refl <- return $ w' `testEquality` w

  ser w bv === Just a

serdeTests :: TestTree
serdeTests = testGroup "serialization/deseriallization tests"
  [ testProperty "bitsBE" $
    serdeTest anyWidth (\w bv -> Just (BV.asBitsBE w bv)) BV.bitsBE
  , testProperty "bitsLE" $
    serdeTest anyWidth (\w bv -> Just (BV.asBitsLE w bv)) BV.bitsLE
  , testProperty "bytesBE" $
    serdeTest byteWidth BV.asBytesBE BV.bytesBE
  , testProperty "bytesLE" $
    serdeTest byteWidth BV.asBytesLE BV.bytesLE
  , testProperty "bytestringBE" $
    serdeTest byteWidth BV.asBytestringBE BV.bytestringBE
  , testProperty "bytestringLE" $
    serdeTest byteWidth BV.asBytestringLE BV.bytestringLE
  ]

deserTests :: TestTree
deserTests = testGroup "deserialization/serialization tests"
  [ testProperty "asBitsBE" $
    deserTest bits length BV.bitsBE (\w bv -> Just (BV.asBitsBE w bv))
  , testProperty "asBitsLE" $
    deserTest bits length BV.bitsLE (\w bv -> Just (BV.asBitsLE w bv))
  , testProperty "asBytesBE" $
    deserTest bytes ((*8) . length) BV.bytesBE BV.asBytesBE
  , testProperty "asBytesLE" $
    deserTest bytes ((*8) . length) BV.bytesLE BV.asBytesLE
  , testProperty "asBytesBE" $
    deserTest (BS.pack <$> bytes) ((*8) . BS.length) BV.bytestringBE BV.asBytestringBE
  , testProperty "asBytesLE" $
    deserTest (BS.pack <$> bytes) ((*8) . BS.length) BV.bytestringLE BV.asBytestringLE
  ]

checkBounds :: MonadTest m => Integer -> NatRepr w -> m ()
checkBounds x w = do
  diff 0 (<=) x
  diff x (<=) (2 ^ natValue w)

wfCtor :: Gen (Some NatRepr)
       -- ^ generator for width
       -> (forall w . NatRepr w -> Integer -> Maybe (BV.BV w))
       -- ^ constructor
       -> Property
wfCtor genW ctor = property $ do
  Some w <- forAll genW
  x <- forAll (largeSigned w)

  case ctor w x of
    Just (BV.BV x') -> checkBounds x' w
    Nothing -> return ()

wfCtor' :: NatRepr w
        -- ^ fixed width of constructor
        -> (Integer -> BV.BV w)
        -- ^ embedding of integer into constructor arg
        -> Property
wfCtor' w ctor = property $ do
  x <- forAll (largeSigned w)

  let BV.BV x' = ctor x

  checkBounds x' w

wfUnary :: Gen (Some NatRepr)
        -- ^ generator for width
        -> (forall w . NatRepr w -> BV.BV w -> BV.BV w)
        -- ^ unary operator
        -> Property
wfUnary genW op = property $ do
  Some w <- forAll genW
  bv <- BV.mkBV w <$> forAll (unsigned w)

  let BV.BV x' = op w bv
  checkBounds x' w

wfUnaryMaybe :: Gen (Some NatRepr)
             -- ^ generator for width
             -> (forall w . NatRepr w -> BV.BV w -> Maybe (BV.BV w))
             -- ^ unary operator
             -> Property
wfUnaryMaybe genW op = property $ do
  Some w <- forAll genW
  bv <- BV.mkBV w <$> forAll (unsigned w)

  case op w bv of
    Just (BV.BV x') -> checkBounds x' w
    Nothing -> return ()

wfBinary :: Gen (Some NatRepr)
         -- ^ generator for width
         -> (forall w . NatRepr w -> BV.BV w -> BV.BV w -> BV.BV w)
         -- ^ binary operator
         -> Property
wfBinary genW op = property $ do
  Some w <- forAll genW
  bv1 <- BV.mkBV w <$> forAll (unsigned w)
  bv2 <- BV.mkBV w <$> forAll (unsigned w)

  let BV.BV x' = op w bv1 bv2
  checkBounds x' w

wfBinaryDiv :: Gen (Some NatRepr)
            -- ^ generator for width
            -> (forall w . NatRepr w -> BV.BV w -> BV.BV w -> BV.BV w)
            -- ^ binary division-like operator
            -> Property
wfBinaryDiv genW op = property $ do
  Some w <- forAll genW
  bv1 <- BV.mkBV w <$> forAll (unsigned w)
  bv2 <- BV.mkBV w <$> forAll (unsignedPos w)

  let BV.BV x' = op w bv1 bv2
  checkBounds x' w

wfBinaryN :: Gen (Some NatRepr)
          -- ^ generator for width
          -> (forall w . NatRepr w -> BV.BV w -> Natural -> BV.BV w)
          -- ^ binary operator with Natural arg
          -> Property
wfBinaryN genW op = property $ do
  Some w <- forAll genW
  bv <- BV.mkBV w <$> forAll (unsigned w)
  n <- fromInteger <$> forAll (largeUnsigned w)

  let BV.BV x' = op w bv n
  checkBounds x' w

wfBit :: Gen (Some NatRepr)
      -- ^ generator for width
      -> (forall w ix . ix+1 <= w => NatRepr w -> NatRepr ix -> BV.BV w -> BV.BV w)
      -- ^ bit twiddling function
      -> Property
wfBit genW f = property $ do
  Some w <- forAll genW
  bv <- BV.mkBV w <$> forAll (unsigned w)
  NatReprLt ix <- forAll (natReprLt w)

  let BV.BV x = f w ix bv
  checkBounds x w

wfBitN :: Gen (Some NatRepr)
       -- ^ generator for width
       -> (forall w . NatRepr w -> Natural -> BV.BV w -> BV.BV w)
       -- ^ bit twiddling function
       -> Property
wfBitN genW f = property $ do
  Some w <- forAll genW
  bv <- BV.mkBV w <$> forAll (unsigned w)
  n <- fromInteger <$> forAll (largeUnsigned w)

  let BV.BV x = f w n bv
  checkBounds x w

wellFormedTests :: TestTree
wellFormedTests = testGroup "well-formedness tests"
  [ testProperty "mkBV" $ wfCtor anyWidth (fmap Just . BV.mkBV)
  , testProperty "mkBVUnsigned" $ wfCtor anyWidth BV.mkBVUnsigned
  , testProperty "mkBVSigned" $ wfCtor anyPosWidth (forcePos BV.mkBVSigned)
  , testProperty "signedClamp" $ wfCtor anyPosWidth (fmap Just . forcePos BV.signedClamp)
  , testProperty "minUnsigned" $ wfCtor anyWidth (\w _ -> Just (BV.minUnsigned w))
  , testProperty "maxUnsigned" $ wfCtor anyWidth (\w _ -> Just (BV.maxUnsigned w))
  , testProperty "minSigned" $ wfCtor anyPosWidth (\w _ -> Just (forcePos BV.minSigned w))
  , testProperty "maxSigned" $ wfCtor anyPosWidth (\w _ -> Just (forcePos BV.maxSigned w))
  , testProperty "bool" $ wfCtor' knownNat (BV.bool . odd)
  , testProperty "word8" $ wfCtor' knownNat (BV.word8 . fromInteger)
  , testProperty "word16" $ wfCtor' knownNat (BV.word16 . fromInteger)
  , testProperty "word32" $ wfCtor' knownNat (BV.word32 . fromInteger)
  , testProperty "word64" $ wfCtor' knownNat (BV.word64 . fromInteger)
  , testProperty "int8" $ wfCtor' knownNat (BV.int8 . fromInteger)
  , testProperty "int16" $ wfCtor' knownNat (BV.int16 . fromInteger)
  , testProperty "int32" $ wfCtor' knownNat (BV.int32 . fromInteger)
  , testProperty "int64" $ wfCtor' knownNat (BV.int64 . fromInteger)
  , testProperty "and" $ wfBinary anyWidth (const BV.and)
  , testProperty "or" $ wfBinary anyWidth (const BV.or)
  , testProperty "xor" $ wfBinary anyWidth (const BV.xor)
  , testProperty "complement" $ wfUnary anyWidth BV.complement
  , testProperty "shl" $ wfBinaryN anyWidth BV.shl
  , testProperty "ashr" $ wfBinaryN anyPosWidth (forcePos BV.ashr)
  , testProperty "lshr" $ wfBinaryN anyWidth BV.lshr
  , testProperty "rotateL" $ wfBinaryN anyWidth BV.rotateL
  , testProperty "rotateR" $ wfBinaryN anyWidth BV.rotateR
  , testProperty "bit" $ property $ do
      Some w <- forAll anyPosWidth
      NatReprLt i <- forAll (natReprLt w)

      let BV.BV x = BV.bit w i
      checkBounds x w
  , testProperty "bit'" $ property $ do
      Some w <- forAll anyPosWidth
      n <- forAll $ Gen.integral $ Range.linear 0 (2 * natValue w)

      let BV.BV x = BV.bit' w n
      checkBounds x w
  , testProperty "setBit" $ wfBit anyPosWidth (const BV.setBit)
  , testProperty "setBit'" $ wfBitN anyPosWidth BV.setBit'
  , testProperty "clearBit" $ wfBit anyPosWidth BV.clearBit
  , testProperty "clearBit'" $ wfBitN anyPosWidth BV.clearBit'
  , testProperty "complementBit" $ wfBit anyPosWidth (const BV.complementBit)
  , testProperty "complementBit'" $ wfBitN anyPosWidth BV.complementBit'
  , testProperty "popCount" $ wfUnary anyWidth (const BV.popCount)
  , testProperty "ctz" $ wfUnary anyWidth BV.ctz
  , testProperty "clz" $ wfUnary anyWidth BV.clz
  , testProperty "truncBits" $ property $ do
      Some w <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)
      n <- forAll $ Gen.integral $ Range.linear 0 (2 * natValue w)

      let BV.BV x = BV.truncBits n bv
      checkBounds x w
  , testProperty "add" $ wfBinary anyWidth BV.add
  , testProperty "sub" $ wfBinary anyWidth BV.sub
  , testProperty "mul" $ wfBinary anyWidth BV.mul
  , testProperty "uquot" $ wfBinaryDiv anyPosWidth (const BV.uquot)
  , testProperty "urem" $ wfBinaryDiv anyPosWidth (const BV.urem)
  , testProperty "squot" $ wfBinaryDiv anyPosWidth (forcePos BV.squot)
  , testProperty "srem" $ wfBinaryDiv anyPosWidth (forcePos BV.srem)
  , testProperty "sdiv" $ wfBinaryDiv anyPosWidth (forcePos BV.sdiv)
  , testProperty "smod" $ wfBinaryDiv anyPosWidth (forcePos BV.smod)
  , testProperty "abs" $ wfUnary anyPosWidth (forcePos BV.abs)
  , testProperty "negate" $ wfUnary anyWidth BV.negate
  , testProperty "signBit" $ wfUnary anyPosWidth (forcePos BV.signBit)
  , testProperty "signum" $ wfUnary anyPosWidth (forcePos BV.signum)
  , testProperty "umin" $ wfBinary anyWidth (const BV.umin)
  , testProperty "umax" $ wfBinary anyWidth (const BV.umax)
  , testProperty "smin" $ wfBinary anyPosWidth (forcePos BV.smin)
  , testProperty "smax" $ wfBinary anyPosWidth (forcePos BV.smax)
  , testProperty "concat" $ property $ do
      Some w <- forAll anyWidth
      Some w' <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)
      bv' <- BV.mkBV w' <$> forAll (unsigned w')

      let BV.BV x = BV.concat w w' bv bv'
      checkBounds x (w `addNat` w')
  , testProperty "select" $ property $ do
      Some w <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)
      NatReprLte ix <- forAll (natReprLte w)
      Just LeqProof <- return $ ix `testLeq` w
      NatReprLte w' <- forAll (natReprLte (w `subNat` ix))
      Just LeqProof <- return $ (ix `addNat` w') `testLeq` w

      let BV.BV x = BV.select ix w' bv
      checkBounds x w'
  , testProperty "select'" $ property $ do
      Some w <- forAll anyWidth
      Some w' <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)
      n <- forAll $ Gen.integral $ Range.linear 0 (2 * natValue w)

      let BV.BV x = BV.select' n w' bv
      checkBounds x w'
  , testProperty "zext" $ property $ do
      Some w' <- forAll anyPosWidth
      NatReprLt w <- forAll (natReprLt w')
      bv <- BV.mkBV w <$> forAll (unsigned w)

      let BV.BV x = BV.zext w' bv
      checkBounds x w'
  , testProperty "sext" $ property $ do
      Some w' <- forAll anyWidthGT1
      NatReprPosLt w <- forAll (natReprPosLt w')
      bv <- BV.mkBV w <$> forAll (unsigned w)

      let BV.BV x = BV.sext w w' bv
      checkBounds x w'
  , testProperty "trunc" $ property $ do
      Some w <- forAll anyPosWidth
      NatReprLt w' <- forAll (natReprLt w)
      bv <- BV.mkBV w <$> forAll (unsigned w)

      let BV.BV x = BV.trunc w' bv
      checkBounds x w'
  , testProperty "trunc'" $ property $ do
      Some w <- forAll anyWidth
      Some w' <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)

      let BV.BV x = BV.trunc' w' bv
      checkBounds x w'
  , testProperty "mulWide" $ property $ do
      Some w <- forAll anyWidth
      Some w' <- forAll anyWidth
      bv <- BV.mkBV w <$> forAll (unsigned w)
      bv' <- BV.mkBV w' <$> forAll (unsigned w')

      let BV.BV x = BV.mulWide w w' bv bv'
      checkBounds x (w `addNat` w')
    , testProperty "succUnsigned" $ wfUnaryMaybe anyWidth BV.succUnsigned
    , testProperty "succSigned" $ wfUnaryMaybe anyPosWidth (forcePos BV.succUnsigned)
    , testProperty "predUnsigned" $ wfUnaryMaybe anyWidth BV.predUnsigned
    , testProperty "predSigned" $ wfUnaryMaybe anyPosWidth (forcePos BV.predUnsigned)
    ]

randomTests :: TestTree
randomTests = testGroup "tests for random generation"
  [ testProperty "randomUnsigned" $ property $ do
      BV.UnsignedBV (BV.BV x) :: BV.UnsignedBV 32 <- liftIO $ getRandom
      checkBounds x (knownNat @32)
  , testProperty "randomSigned" $ property $ do
      BV.SignedBV (BV.BV x) :: BV.SignedBV 32 <- liftIO $ getRandom
      checkBounds x (knownNat @32)
  ]

tests :: TestTree
tests = testGroup "bv-sized tests"
  [ arithHomTests
  , bitwiseHomTests
  , serdeTests
  , deserTests
  , wellFormedTests
  , randomTests
  ]

main :: IO ()
main = defaultMain tests
