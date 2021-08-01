module PrimeField.Montgomery1
  ( T(..)
  , prop_homomorphism
  ) where

import           Prelude            ((<$>))
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (type CLog)
import           GHC.TypeNats       (type (<=))

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.IntegralDomain
import qualified Algebra.Laws
import qualified Algebra.Ring

import           Clash.Prelude (BitPack(..))
import qualified PrimeField
import           Utils         (floorDivByTwoToThePowerOf, modTwoToThePowerOf, multByTwoToThePowerOf)

-- $

newtype T r t = Cons { decons :: t } deriving
  (Algebra.Additive.C, Algebra.Ring.C, BitPack, Eq, Functor, Show)

logP :: Proxy r -> Proxy (CLog 2 r)
logP _ = Proxy

radixP :: T r t -> Proxy r
radixP _ = Proxy

logRadix :: (KnownNat r, 2 <= r) => T r t -> Int
logRadix = fromInteger . natVal . logP . radixP

--

divByR :: (KnownNat r, 2 <= r, BitPack t) => T r t -> T r t
divByR x = flip floorDivByTwoToThePowerOf (logRadix x) <$> x

modR :: (KnownNat r, 2 <= r, Algebra.Ring.C t, BitPack t) => T r t -> T r t
modR x = flip modTwoToThePowerOf (logRadix x) <$> x

multByR :: (KnownNat r, 2 <= r, BitPack t) => T r t -> T r t
multByR x = flip multByTwoToThePowerOf (logRadix x) <$> x

--

instance (KnownNat p, KnownNat q, KnownNat r, 2 <= r, Algebra.IntegralDomain.C t, BitPack t, Eq t, Ord t, Show t) => (PrimeField.C p q (T r t)) where
  x `into` (modP, _) = Cons $ decons (multByR x) `mod` fromInteger (natVal modP)
  outfrom = PrimeField.reduce2
  (Cons x) `reduce1` (modP, _) = Cons $ if x < p then x else x - p where p = fromInteger (natVal modP)
  x `reduce2` (modP, auxP) = x' `PrimeField.reduce1` (modP, auxP) where
    a = modR x
    b = a * fromInteger p'
    c = modR b
    d = x + c * fromInteger p
    x' = divByR d
    p' = natVal auxP
    p = natVal modP
  inverse = PrimeField.fermatInverse

--

prop_homomorphism
  :: (PrimeField.C p q t, PrimeField.C p q (T r t))
  => (Proxy p, Proxy q)
  -> (PrimeField.T p q (T r t) -> PrimeField.T p q (T r t) -> PrimeField.T p q (T r t))
  -> (PrimeField.T p q t -> PrimeField.T p q t -> PrimeField.T p q t)
  -> PrimeField.T p q (T r t) -> PrimeField.T p q (T r t) -> Bool
prop_homomorphism modP = Algebra.Laws.homomorphism phi where
  phi (PrimeField.T x) = PrimeField.T $ decons (x `PrimeField.outfrom` modP) `PrimeField.into` modP
