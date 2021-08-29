module Tests.PrimeField where

import Prelude

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck.Hedgehog

import qualified Algebra.Field
import qualified Algebra.Ring
import qualified MathObj.Wrapper.Haskell98 as W

import qualified PrimeField
import qualified PrimeField.Montgomery1
import qualified PrimeField.MontgomeryN

--

type P = 113
type P' = 111
type R1 = W.T Int -- euclidInverse only works with signed store types
type R1' = W.T Word

instance Arbitrary (PrimeField.T P P' R1)  where arbitrary = hedgehog $ PrimeField.gen     @P @P' @R1
instance Arbitrary (PrimeField.T P P' R1') where arbitrary = hedgehog $ PrimeField.genUnit @P @P' @R1'

type R2 = PrimeField.Montgomery1.T 128 (W.T Word)
instance Arbitrary (PrimeField.T P P' R2) where arbitrary = hedgehog $ PrimeField.genUnit @P @P' @R2

type R3 = PrimeField.MontgomeryN.T 2 7 (W.T Word)
instance Arbitrary (PrimeField.T P 1 R3) where arbitrary = hedgehog $ PrimeField.genUnit @P @1 @R3

tests :: TestTree
tests = testGroup "Tests.PrimeField"
  [ testProperty "Algebra.Ring.propLeftDistributive"               $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P P' R1')
  , testProperty "Algebra.Ring.propRightDistributive"              $ Algebra.Ring.propRightDistributive @(PrimeField.T P P' R1')
  , testProperty "Algebra.Field.propReciprocal"                    $ Algebra.Field.propReciprocal       @(PrimeField.T P P' R1)
  , testProperty "Montgomery1: Algebra.Ring.propLeftDistributive"  $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P P' R2)
  , testProperty "Montgomery1: Algebra.Ring.propRightDistributive" $ Algebra.Ring.propRightDistributive @(PrimeField.T P P' R2)
  , testProperty "Montgomery1: Algebra.Field.propReciprocal"       $ Algebra.Field.propReciprocal       @(PrimeField.T P P' R2)
  , testProperty "MontgomeryN: Algebra.Ring.propLeftDistributive"  $ Algebra.Ring.propLeftDistributive  @(PrimeField.T P 1 R3)
  , testProperty "MontgomeryN: Algebra.Ring.propRightDistributive" $ Algebra.Ring.propRightDistributive @(PrimeField.T P 1 R3)
  , testProperty "MontgomeryN: Algebra.Field.propReciprocal"       $ Algebra.Field.propReciprocal       @(PrimeField.T P 1 R3)
  ]

main :: IO ()
main = defaultMain tests
