import Prelude

import Test.Tasty

import qualified Tests.PrimeField

main :: IO ()
main = defaultMain $ testGroup "."
  [ Tests.PrimeField.tests
  ]
