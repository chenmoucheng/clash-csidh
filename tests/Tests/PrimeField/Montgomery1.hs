module Tests.PrimeField.Montgomery1 where

import Prelude (Word)

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.Hedgehog

import qualified Hedgehog as H

import           NumericPrelude
import qualified MathObj.Wrapper.Haskell98 as W

import qualified PrimeField.Montgomery1
import qualified PrimeField

--

prop_additiveHomomorphism :: H.Property
prop_additiveHomomorphism =
  H.property $ do
    x <- H.forAll $ PrimeField.gen @113 @111
    y <- H.forAll $ PrimeField.gen @113 @111
    H.assert $ PrimeField.Montgomery1.prop_homomorphism @113 @111 @128 @(W.T Word) (+) (+) x y

prop_multiplicativeHomomorphism :: H.Property
prop_multiplicativeHomomorphism =
  H.property $ do
    x <- H.forAll $ PrimeField.genUnit @113 @111
    y <- H.forAll $ PrimeField.genUnit @113 @111
    H.assert $ PrimeField.Montgomery1.prop_homomorphism @113 @111 @128 @(W.T Word) (*) (*) x y

--

tests :: TestTree
tests = $(testGroupGenerator)

main :: IO ()
main = defaultMain tests
