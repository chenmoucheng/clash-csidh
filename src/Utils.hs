module Utils where

import           Data.Bits    (Bits(..), FiniteBits(..))
import           Data.Proxy   (Proxy(..))
import           GHC.TypeNats (KnownNat)

import           NumericPrelude
import qualified Algebra.Ring

import qualified Clash.Prelude as C

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

composeN :: forall n a. (KnownNat n) => (a -> a) -> a -> a
composeN = C.foldr (.) id . C.repeat @n

--

foldrBits :: (C.BitPack t) => (a -> a) -> (a -> a) -> a -> t -> a
foldrBits t f z b = fst $ until g h (z, bn) where
  g (_, i) = i < 0
  h (x, i) = (if testBit bv i then t x else f x, i - 1)
  bn = finiteBitSize bv - 1 - countLeadingZeros bv
  bv = C.pack b
