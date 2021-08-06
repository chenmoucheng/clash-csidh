module PrimeField.Montgomery1
  ( C
  , T
  , prop_homomorphism
  ) where

import           Prelude            (Integral)
import           Data.Function      ((&))
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

deriving instance (C r t) => (Algebra.Absolute.C       (T r t))
deriving instance (C r t) => (Algebra.Additive.C       (T r t))
deriving instance (C r t) => (Algebra.IntegralDomain.C (T r t))
deriving instance (C r t) => (Algebra.RealIntegral.C   (T r t))
deriving instance (C r t) => (Algebra.Ring.C           (T r t))
deriving instance (C r t) => (Algebra.ToInteger.C      (T r t))
deriving instance (C r t) => (Algebra.ToRational.C     (T r t))
deriving instance (C r t) => (Algebra.ZeroTestable.C   (T r t))

--

reduce1 :: forall p r t. (KnownNat p, C r t) => T r t -> T r t
reduce1 x = if x < p then x else x - p where p = fromInteger $ natVal @p Proxy

reduce2 :: forall p q r t. (KnownNat p, KnownNat q, C r t) => T r t -> T r t
reduce2 x = x' & reduce1 @p @r where
  a = x & modulo @r
  b = a * fromInteger p'
  c = b & modulo @r
  d = x + c * fromInteger p
  x' = d & floorDivBy @r
  p' = natVal @q Proxy
  p = natVal @p Proxy

instance (KnownNat p, 2 <= p, KnownNat q, C r t) => (PrimeField.C p q (T r t)) where
  into = fromInteger . flip mod (natVal @p Proxy) .  (natVal @r Proxy *)
  outfrom = toInteger . reduce2 @p @q @r
  addMod = reduce1 @p    @r `compose2` (+) where compose2 = (.) . (.)
  mulMod = reduce2 @p @q @r `compose2` (*) where compose2 = (.) . (.)
  invMod = PrimeField.fermatInverse @p @q

--

prop_homomorphism
  :: forall p q r t. (PrimeField.C p q t, PrimeField.C p q (T r t))
  => (PrimeField.T p q t -> PrimeField.T p q t -> PrimeField.T p q t)
  -> (PrimeField.T p q (T r t) -> PrimeField.T p q (T r t) -> PrimeField.T p q (T r t))
  -> PrimeField.T p q t -> PrimeField.T p q t -> Bool
prop_homomorphism = Algebra.Laws.homomorphism phi where
  phi = fmap $ PrimeField.into @p @q @(T r t) . PrimeField.outfrom @p @q @t
