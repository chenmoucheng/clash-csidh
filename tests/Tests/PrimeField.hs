module Tests.PrimeField where

import Prelude
import Data.Proxy (Proxy (..))

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck.Hedgehog

import qualified NumericPrelude
import qualified Algebra.Field
import qualified Algebra.Ring
import qualified MathObj.Wrapper.Haskell98 as W

import qualified PrimeField
import qualified PrimeField.Montgomery1

--

type P = 113
type R1 = W.T Word
type R1' = W.T Int

instance Arbitrary (PrimeField.T P R1)  where arbitrary = hedgehog $ PrimeField.gen     @P @R1  Proxy
instance Arbitrary (PrimeField.T P R1') where arbitrary = hedgehog $ PrimeField.genUnit @P @R1' Proxy

type R2 = PrimeField.Montgomery1.T 128 NumericPrelude.Int
instance Arbitrary (PrimeField.T P R2) where arbitrary = hedgehog $ PrimeField.genUnit @P @R2 Proxy

tests :: TestTree
tests = testGroup "Tests.PrimeField"
  [ testProperty "Algebra.Ring.propLeftDistributive"               $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P R1')
  , testProperty "Algebra.Ring.propRightDistributive"              $ Algebra.Ring.propRightDistributive @(PrimeField.T P R1')
  , testProperty "Algebra.Field.propReciprocal"                    $ Algebra.Field.propReciprocal       @(PrimeField.T P R1)
  , testProperty "Montgomery1: Algebra.Ring.propLeftDistributive"  $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P R2)
  , testProperty "Montgomery1: Algebra.Ring.propRightDistributive" $ Algebra.Ring.propRightDistributive @(PrimeField.T P R2)
  , testProperty "Montgomery1: Algebra.Field.propReciprocal"       $ Algebra.Field.propReciprocal       @(PrimeField.T P R2)
  ]

main :: IO ()
main = defaultMain tests
