module Tests.PrimeField.MontgomeryN where

import Prelude ()

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.Hedgehog

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified MathObj.Wrapper.Haskell98 as W

import qualified Clash.Prelude as C
import qualified PrimeField.MontgomeryN
import qualified PrimeField

--

prop_fromIntegerIsAdditiveHomomorphic :: H.Property
prop_fromIntegerIsAdditiveHomomorphic =
  H.property $ do
    x <- H.forAll . Gen.integral $ Range.linear 0 255
    y <- H.forAll . Gen.integral $ Range.linear 0 255
    H.assert $ PrimeField.MontgomeryN.prop_fromIntegerIsHomomorphic @4 @8 @(W.T (C.Unsigned 9)) (+) (+) x y

prop_fromIntegerIsMultiplicativeHomomorphic :: H.Property
prop_fromIntegerIsMultiplicativeHomomorphic =
  H.property $ do
    x <- H.forAll . Gen.integral $ Range.linear 0 127
    y <- H.forAll . Gen.integral $ Range.linear 0 127
    H.assert $ PrimeField.MontgomeryN.prop_fromIntegerIsHomomorphic @2 @14 @(W.T (C.Unsigned 3)) (*) (*) x y

prop_additiveHomomorphism :: H.Property
prop_additiveHomomorphism =
  H.property $ do
    x <- H.forAll $ PrimeField.gen @113 @1
    y <- H.forAll $ PrimeField.gen @113 @1
    H.assert $ PrimeField.MontgomeryN.prop_homomorphism @113 @1 @2 @7 @(W.T (C.Unsigned 3)) (+) (+) x y

prop_multiplicativeHomomorphism :: H.Property
prop_multiplicativeHomomorphism =
  H.property $ do
    x <- H.forAll $ PrimeField.genUnit @113 @1
    y <- H.forAll $ PrimeField.genUnit @113 @1
    H.assert $ PrimeField.MontgomeryN.prop_homomorphism @113 @1 @2 @7 @(W.T (C.Unsigned 3)) (*) (*) x y

--

tests :: TestTree
tests = $(testGroupGenerator)

main :: IO ()
main = defaultMain tests
