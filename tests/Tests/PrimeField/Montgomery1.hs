module Tests.PrimeField.Montgomery1 where

import Prelude    (Word)
import Data.Proxy (Proxy (..))

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.Hedgehog

import qualified Hedgehog as H

import           NumericPrelude
import qualified MathObj.Wrapper.Haskell98 as W

import qualified PrimeField.Montgomery1
import qualified PrimeField

--

prop_outfromIsAdditiveHomomorphic :: H.Property
prop_outfromIsAdditiveHomomorphic =
  H.property $ do
    x <- H.forAll $ PrimeField.gen Proxy
    y <- H.forAll $ PrimeField.gen Proxy
    H.assert $ PrimeField.Montgomery1.prop_homomorphism @113 @(W.T Word) @128 Proxy (+) (+) x y

prop_outfromIsMultiplicativeHomomorphic :: H.Property
prop_outfromIsMultiplicativeHomomorphic =
  H.property $ do
    x <- H.forAll $ PrimeField.genUnit Proxy
    y <- H.forAll $ PrimeField.genUnit Proxy
    H.assert $ PrimeField.Montgomery1.prop_homomorphism @113 @(W.T Word) @128 Proxy (*) (*) x y

--

tests :: TestTree
tests = $(testGroupGenerator)

main :: IO ()
main = defaultMain tests
