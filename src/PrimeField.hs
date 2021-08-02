module PrimeField
  ( C(..)
  , T(..)
  , euclidInverse
  , fermatInverse
  , legendreSymbol
  , gen
  , genUnit
  ) where

import           Prelude      (Integral)
import           Data.Proxy   (Proxy(..))
import           GHC.TypeLits (KnownNat, natVal)

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
import           Utils         (floorDivByTwoToThePowerOf, foldrBits)

-- $

class (KnownNat p, KnownNat q, Algebra.Ring.C t, BitPack t, Eq t, Show t) => (C p q t) where
  into :: Integer -> (Proxy p, Proxy q) -> t
  outfrom :: t -> (Proxy p, Proxy q) -> Integer
  reduce1 :: t -> (Proxy p, Proxy q) -> t
  reduce2 :: t -> (Proxy p, Proxy q) -> t
  inverse :: t -> (Proxy p, Proxy q) -> t

--

deriving instance (BitPack t) => (BitPack (W.T t))

instance (KnownNat p, KnownNat q, BitPack t, Eq t, Integral t, Show t) => (C p q (W.T t)) where
  x `into` (modP, _) = fromInteger $ x `mod` natVal modP
  x `outfrom` _ = toInteger x
  x `reduce1` (modP, _) = x `mod` fromInteger (natVal modP)
  reduce2 = reduce1
  inverse = euclidInverse

--

newtype T p q t = T t deriving (Eq, Functor, Show)

modulusPOf :: T p q t -> (Proxy p, Proxy q)
modulusPOf _ = (Proxy, Proxy)

modulusOf :: (KnownNat p, Algebra.Ring.C t) => T p q t -> t
modulusOf = fromInteger . natVal . fst . modulusPOf

--

instance (C p q t) => (Algebra.ZeroTestable.C (T p q t)) where
  isZero = Algebra.ZeroTestable.defltIsZero

instance (C p q t) => (Algebra.Additive.C (T p q t)) where
  zero = T zero
  (T x) + (T y) = let z = T $ (x + y) `reduce1` modulusPOf z in z
  negate (T x) = let z = T $ modulusOf z - x in z

instance (C p q t) => (Algebra.Ring.C (T p q t)) where
  (T x) * (T y) = let z = T $ (x * y) `reduce2` modulusPOf z in z
  fromInteger i
    | i < 0 = negate . fromInteger $ -i
    | otherwise = let z = T $ fromInteger i `into` modulusPOf z in z

instance (C p q t) => (Algebra.Field.C (T p q t)) where
  recip (Algebra.ZeroTestable.isZero -> True) = error "divide by zero"
  recip (T x) = let z = T $ x `inverse` modulusPOf z in z

--

toThePowerOf :: (C p q t) => T p q t -> t -> T p q t
toThePowerOf x = foldrBits sm s 1 where
  sm = (x *) . s
  s = Algebra.Ring.sqr

euclidInverse :: (C p q t, Algebra.IntegralDomain.C t, Ord t) => t -> (Proxy p, Proxy q) -> t
z `euclidInverse` (modP, _) = if z' > 0 then z' else z' + p where
  xgcd x y
    | x < 0 = let (g, (a, b)) = xgcd (-x) y in (g, (-a, b))
    | y < 0 = let (g, (a, b)) = xgcd x (-y) in (g, (a, -b))
    | x < y = let (g, (a, b)) = xgcd y x in (g, (b, a))
    | y == 0 = (x, (1, 0))
    | otherwise = let
      (q, r) = x `divMod` y
      (g, (a', b')) = xgcd y r
      in (g, (b', a' - q * b'))
  p = fromInteger (natVal modP)
  (_, (z', _)) = xgcd z p

fermatInverse :: forall p q t. (C p q t) => t -> (Proxy p, Proxy q) -> t
x `fermatInverse` _ = f z where
  f (T _x) = _x
  z = T @p @q @t x `toThePowerOf` (modulusOf z - 2)

legendreSymbol :: (C p q t) => T p q t -> T p q t
legendreSymbol 0 = 0
legendreSymbol x = x `toThePowerOf` (modulusOf x `floorDivByTwoToThePowerOf` 1)

--

gen :: (C p q t, H.MonadGen m) => (Proxy p, Proxy q) -> m (T p q t)
gen (modP, _) = do
  x <- Gen.integral $ Range.linear 0 (natVal modP - 1)
  return $ fromInteger x

genUnit :: (C p q t, H.MonadGen m) => (Proxy p, Proxy q) -> m (T p q t)
genUnit (modP, _) = do
  x <- Gen.integral $ Range.linear 1 (natVal modP - 1)
  return $ fromInteger x
