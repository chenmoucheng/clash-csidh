module Utils where

import           Data.Bits (Bits(..), FiniteBits(..))

import           NumericPrelude
import qualified Algebra.Ring

import           Clash.Prelude (BitPack(..))

-- $

data Ratio a = R a a deriving (Show)
instance (Algebra.Ring.C a, Eq a) => (Eq (Ratio a)) where
  R x1 z1 == R x2 z2 = x1 * z2 == x2 * z1

data EvalEndofunc a = E (a -> a) a
instance (Eq a) => (Eq (EvalEndofunc a)) where
  E f x == E g y = f x == g y

compose :: (Eq a) => EvalEndofunc a -> EvalEndofunc a -> EvalEndofunc a
compose (E f x) (E g y)
  | x == y = E (f . g) x
  | otherwise = error "cannot compose endofunctions evaluated at different inputs"

--

floorDivByTwoToThePowerOf :: (BitPack t) => t -> Int -> t
floorDivByTwoToThePowerOf x r = unpack . flip shiftR r . pack $ x

modTwosPower :: (BitPack t) => t -> t -> t
modTwosPower x = unpack . (pack x .&.) . pack where

multByTwoToThePowerOf :: (BitPack t) => t -> Int -> t
multByTwoToThePowerOf x r = unpack . flip shiftL r . pack $ x

--

foldrBits :: (BitPack t) => (a -> a) -> (a -> a) -> a -> t -> a
foldrBits t f z b = fst $ until g h (z, bn) where
  bv = pack b
  g (_, i) = i < 0
  h (x, i) = (if testBit bv i then t x else f x, i - 1)
  bn = finiteBitSize bv - 1 - countLeadingZeros bv
