module PrimeField.Montgomery1
  ( T(..)
  , prop_homomorphism
  ) where

import           Prelude            ((<$>))
import           Data.Bits          (Bits(..), FiniteBits(..))
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (type CLog)
import           GHC.TypeNats       (type (<=))

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.IntegralDomain
import qualified Algebra.Laws
import qualified Algebra.Ring

import qualified PrimeField

-- $

newtype T r t = Cons { decons :: t } deriving
  (Algebra.Additive.C, Algebra.Ring.C, Bits, Eq, FiniteBits, Functor, Show)

logP :: Proxy r -> Proxy (CLog 2 r)
logP _ = Proxy

radixP :: T r t -> Proxy r
radixP _ = Proxy

radix :: (KnownNat r, Algebra.Ring.C t') => T r t -> t'
radix = fromInteger . natVal . radixP

multByR :: (KnownNat r, 2 <= r, FiniteBits t) => T r t -> T r t
multByR x = flip shiftL (fromInteger . natVal . logP . radixP $ x) <$> x

divByR :: (KnownNat r, 2 <= r, FiniteBits t) => T r t -> T r t
divByR x = flip shiftR (fromInteger . natVal . logP . radixP $ x) <$> x

modR :: (KnownNat r, Algebra.Ring.C t, FiniteBits t) => T r t -> T r t
modR x = (.&.) (radix x - 1) <$> x

--

instance (KnownNat p, KnownNat q, KnownNat r, 2 <= r, Algebra.IntegralDomain.C t, Eq t, FiniteBits t, Ord t, Show t) => (PrimeField.C p q (T r t)) where
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
