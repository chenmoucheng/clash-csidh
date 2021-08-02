module Utils where

import           Data.Bits          (Bits(..), FiniteBits(..))
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (CLog, FLog)
import           GHC.TypeNats       (type (-), type (<=))

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

modulo :: forall r t. (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Algebra.Ring.C t, BitPack t) => t -> Proxy r -> t
modulo x _ = unpack . (pack x .&.) . pack . fromInteger @t $ natVal (Proxy :: Proxy (r - 1))

multByTwoToThePowerOf :: (BitPack t) => t -> Int -> t
multByTwoToThePowerOf x r = unpack . flip shiftL r . pack $ x

--

foldrBits :: (BitPack t) => (a -> a) -> (a -> a) -> a -> t -> a
foldrBits t f z b = fst $ until g h (z, bn) where
  bv = pack b
  g (_, i) = i < 0
  h (x, i) = (if testBit bv i then t x else f x, i - 1)
  bn = finiteBitSize bv - 1 - countLeadingZeros bv
