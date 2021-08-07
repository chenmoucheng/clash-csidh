module PrimeField
  ( C(..)
  , T
  , euclidInverse
  , fermatInverse
  , legendreSymbol
  , gen
  , genUnit
  ) where

import           Prelude       (Integral)
import           Data.Function ((&))
import           Data.Proxy    (Proxy(..))
import           GHC.TypeLits  (KnownNat, natVal)
import           GHC.TypeNats  (type (-), type (<=))

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.Field
import qualified Algebra.IntegralDomain
import qualified Algebra.Ring
import qualified Algebra.ZeroTestable
import qualified MathObj.Wrapper.Haskell98 as W

import           Clash.Prelude (BitPack)
import           Radix2        (floorDivBy)
import           Utils         (foldrBits)

-- $

class (KnownNat p, 2 <= p, KnownNat q, Algebra.Ring.C t, Algebra.ZeroTestable.C t, BitPack t, Eq t, Show t) => (C p q t) where
  into :: Integer -> t
  outfrom :: t -> Integer
  addMod :: t -> t -> t
  mulMod :: t -> t -> t
  invMod :: t -> t

deriving instance (BitPack t) => (BitPack (W.T t))

instance (KnownNat p, 2 <= p, KnownNat q, Integral t, BitPack t, Eq t, Show t) => (C p q (W.T t)) where
  into = fromInteger . flip mod (natVal @p Proxy)
  outfrom = toInteger
  addMod = flip mod (fromInteger $ natVal @p Proxy) `compose2` (+) where compose2 = (.) . (.)
  mulMod = flip mod (fromInteger $ natVal @p Proxy) `compose2` (*) where compose2 = (.) . (.)
  invMod = euclidInverse @p @q

--

newtype T p q t = T t deriving (Eq, Functor, Show)

deriving instance (C p q t) => (Algebra.ZeroTestable.C (T p q t))

instance (C p q t) => (Algebra.Additive.C (T p q t)) where
  zero = T zero
  (T x) + (T y) = T $ x |+| y where (|+|) = addMod @p @q
  negate (T x) = T $ fromInteger (natVal @p Proxy) - x

instance (C p q t) => (Algebra.Ring.C (T p q t)) where
  (T x) * (T y) = T $ x |*| y where (|*|) = mulMod @p @q
  fromInteger i
    | i < 0 = negate . fromInteger $ -i
    | otherwise = T $ i & into @p @q

instance (C p q t) => (Algebra.Field.C (T p q t)) where
  recip (Algebra.ZeroTestable.isZero -> True) = error "divide by zero"
  recip (T x) = T $ x & invMod @p @q

--

toThePowerOf :: forall p q t. (C p q t) => T p q t -> t -> T p q t
toThePowerOf x = foldrBits sm s 1 where
  sm = (x *) . s
  s = Algebra.Ring.sqr

legendreSymbol :: forall p q t. (C p q t) => T p q t -> T p q t
legendreSymbol = flip toThePowerOf $ fromInteger (natVal @p Proxy) & floorDivBy @2

--

euclidInverse :: forall p q t. (C p q t, Algebra.IntegralDomain.C t, Ord t) => t -> t
euclidInverse z = if z' > 0 then z' else z' + p where
  xgcd x y
    | x < 0 = let (g, (a, b)) = xgcd (-x) y in (g, (-a, b))
    | y < 0 = let (g, (a, b)) = xgcd x (-y) in (g, (a, -b))
    | x < y = let (g, (a, b)) = xgcd y x in (g, (b, a))
    | y == 0 = (x, (1, 0))
    | otherwise = let
      (q, r) = x `divMod` y
      (g, (a', b')) = xgcd y r
      in (g, (b', a' - q * b'))
  (_, (z', _)) = xgcd z p
  p = fromInteger $ natVal @p Proxy

fermatInverse :: forall p q t. (C p q t) => t -> t
fermatInverse = f . flip toThePowerOf (fromInteger (natVal @p Proxy) - 2) . T @p @q where f (T x) = x

--

gen :: forall p q t m. (C p q t, H.MonadGen m) => m (T p q t)
gen = do
  x <- Gen.integral $ Range.linear 0 (natVal @(p - 1) Proxy)
  return $ fromInteger x

genUnit :: forall p q t m. (C p q t, H.MonadGen m) => m (T p q t)
genUnit = do
  x <- Gen.integral $ Range.linear 1 (natVal @(p - 1) Proxy)
  return $ fromInteger x
