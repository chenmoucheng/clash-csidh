module PrimeField.Montgomery1
  ( C
  , T
  , prop_homomorphism
  ) where

import           Prelude            (Integral)
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (CLog, FLog)
import           GHC.TypeNats       (type (<=))

import           NumericPrelude
import qualified Algebra.Absolute
import qualified Algebra.Additive
import qualified Algebra.IntegralDomain
import qualified Algebra.Laws
import qualified Algebra.RealIntegral
import qualified Algebra.Ring
import qualified Algebra.ToInteger
import qualified Algebra.ToRational
import qualified Algebra.ZeroTestable
import qualified MathObj.Wrapper.Haskell98 as W

import           Clash.Prelude (BitPack(..))
import qualified PrimeField
import           Radix2        (floorDivBy, modulo)

-- $

class (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Algebra.ToInteger.C t, BitPack t, Eq t, Ord t, Show t) => (C r t)

instance (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Integral t, BitPack t, Eq t, Ord t, Show t) => (C r (W.T t))

--

newtype T r t = T t deriving (BitPack, Eq, Ord, Show)

deriving instance (C r t) => (Algebra.Absolute.C     (T r t))
deriving instance (C r t) => (Algebra.Additive.C     (T r t))
deriving instance (C r t) => (Algebra.IntegralDomain.C     (T r t))
deriving instance (C r t) => (Algebra.RealIntegral.C (T r t))
deriving instance (C r t) => (Algebra.Ring.C         (T r t))
deriving instance (C r t) => (Algebra.ToInteger.C    (T r t))
deriving instance (C r t) => (Algebra.ToRational.C   (T r t))
deriving instance (C r t) => (Algebra.ZeroTestable.C (T r t))

--

reduce1 :: forall p r t. (KnownNat p, C r t) => T r t -> Proxy p -> T r t
reduce1 x _ = if x < p then x else x - p where p = fromInteger (natVal @p Proxy)

reduce2 :: forall p q r t. (KnownNat p, KnownNat q, C r t) => T r t -> (Proxy p, Proxy q) -> T r t
reduce2 x _ = x' `reduce1` (Proxy :: Proxy p) where
  a = x `modulo` (Proxy :: Proxy r)
  b = a * fromInteger p'
  c = b `modulo` (Proxy :: Proxy r)
  d = x + c * fromInteger p
  x' = d `floorDivBy` (Proxy :: Proxy r)
  p' = natVal @q Proxy
  p = natVal @p Proxy

instance (KnownNat p, 2 <= p, KnownNat q, C r t) => (PrimeField.C p q (T r t)) where
  into x _ = fromInteger $ x * natVal @r Proxy `mod` natVal @p Proxy
  outfrom = toInteger `compose2` reduce2 where compose2 = (.) . (.)
  addMod (x, y) = reduce1 (x + y) . fst
  mulMod (x, y) = reduce2 (x * y)
  invMod = PrimeField.fermatInverse

--

prop_homomorphism
  :: (PrimeField.C p q t, PrimeField.C p q (T r t))
  => (Proxy p, Proxy q)
  -> (PrimeField.T p q t -> PrimeField.T p q t -> PrimeField.T p q t)
  -> (PrimeField.T p q (T r t) -> PrimeField.T p q (T r t) -> PrimeField.T p q (T r t))
  -> PrimeField.T p q t -> PrimeField.T p q t -> Bool
prop_homomorphism proxies = Algebra.Laws.homomorphism phi where
  phi = fmap $ flip PrimeField.into proxies . flip PrimeField.outfrom proxies
