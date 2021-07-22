module Tests.PrimeField where

import Prelude

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.Hedgehog

import Hedgehog ((===))
import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen

import PrimeField

tests :: TestTree
tests = $(testGroupGenerator)

main :: IO ()
main = defaultMain tests

