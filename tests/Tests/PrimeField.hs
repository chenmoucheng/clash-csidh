{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}

module Tests.PrimeField where

import Prelude
import Data.Proxy (Proxy (..))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck.Hedgehog

import qualified Algebra.Field
import qualified Algebra.Ring
import qualified MathObj.Wrapper.Haskell98 as W

import qualified PrimeField

--

type P = 127
type Fp = W.T Word
type FpUnits = W.T Int

instance Arbitrary (PrimeField.T P Fp)      where arbitrary = hedgehog $ PrimeField.gen     @P @Fp      Proxy
instance Arbitrary (PrimeField.T P FpUnits) where arbitrary = hedgehog $ PrimeField.genUnit @P @FpUnits Proxy

tests :: TestTree
tests = testGroup "PrimeField"
  [ testProperty "Algebra.Ring.propLeftDistributive"  $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P Fp)
  , testProperty "Algebra.Ring.propRightDistributive" $ Algebra.Ring.propRightDistributive @(PrimeField.T P Fp)
  , testProperty "Algebra.Field.propReciprocal"       $ Algebra.Field.propReciprocal       @(PrimeField.T P FpUnits)
  ]

main :: IO ()
main = defaultMain tests
