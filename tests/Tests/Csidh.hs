{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}

module Tests.Csidh where

import Prelude    ((<$>))
import Data.Proxy (Proxy (..))

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.Hedgehog

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified MathObj.Wrapper.Haskell98 as W

import qualified Clash.Prelude as C
import qualified PrimeField
import qualified Csidh

--

type Store = W.T (C.Unsigned 1024)
type Fp = Csidh.K Store

prop_scalarMultiplicationIsHomomorphic :: H.Property
prop_scalarMultiplicationIsHomomorphic =
  H.property $ do
    n <- H.forAll . Gen.integral $ Range.linear 0 30
    m <- H.forAll . Gen.integral $ Range.linear 0 30
    x <- H.forAll $ PrimeField.gen Proxy
    z <- H.forAll $ PrimeField.gen Proxy
    H.assert $ Csidh.prop_scalarMultiplicationIsHomomorphic @Csidh.Scalar @Fp n m x z

prop_groupActionCommutesWithStoreMultiplication :: H.Property
prop_groupActionCommutesWithStoreMultiplication =
  H.property $ do
    i <- H.forAll . Gen.integral $ Range.linear 0 (length Csidh.ells - 1)
    let ell = Csidh.ells C.!! i
    let f x = Csidh.ellTorsionPoint (ell, x, 1, 0)
    x <- H.forAll $ Gen.filter ((0 /=) . snd . f) (PrimeField.gen Proxy)
    let (xQ, zQ) = f x
    n <- H.forAll . Gen.integral $ Range.linear 1 1000
    H.assert $ Csidh.prop_groupActionCommutesWithScalarMultiplication @Csidh.Scalar @Fp ell (xQ / zQ) n x

prop_groupActionIsCommutative :: H.Property
prop_groupActionIsCommutative =
  H.property $ do
    skA <- H.forAll Csidh.genkey2
    skB <- H.forAll Csidh.genkey2
    let xPs = PrimeField.T <$> C.iterateI (1 +) 1
    H.assert $ Csidh.prop_groupActionIsCommutative @1000 @Store skA skB xPs

--

tests :: TestTree
tests = $(testGroupGenerator)

main :: IO ()
main = defaultMain tests
