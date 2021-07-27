import Prelude

import Test.Tasty

import qualified Tests.PrimeField
import qualified Tests.Csidh

main :: IO ()
main = defaultMain $ testGroup "."
  [ Tests.PrimeField.tests
  , Tests.Csidh.tests
  ]
