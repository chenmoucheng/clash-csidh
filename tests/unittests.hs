import Prelude

import Test.Tasty

import qualified Tests.PrimeField.Montgomery1
import qualified Tests.PrimeField
import qualified Tests.Csidh

main :: IO ()
main = defaultMain $ testGroup "."
  [ Tests.PrimeField.Montgomery1.tests
  , Tests.PrimeField.tests
  , Tests.Csidh.tests
  ]
