module PrimeField.Montgomery1
  ( T(..)
  , prop_homomorphism
  ) where

import           Prelude            ((<$>))
import           Data.Proxy         (Proxy(..))
import           GHC.TypeLits       (KnownNat, natVal)
import           GHC.TypeLits.Extra (type CLog, FLog, Log)
import           GHC.TypeNats       (type (<=))

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.Laws
import qualified Algebra.Ring
import qualified Algebra.ToInteger

import           Clash.Prelude (BitPack(..))
import qualified PrimeField
import           Utils         (floorDivByTwoToThePowerOf, modulo, multByTwoToThePowerOf)

-- $

newtype T r t = Cons { decons :: t } deriving (Algebra.Additive.C, Algebra.Ring.C, BitPack, Eq, Functor, Ord, Show)

radixP :: T r t -> Proxy r
radixP _ = Proxy

logP :: Proxy r -> Proxy (Log 2 r)
logP _ = Proxy

logRadix :: (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r) => T r t -> Int
logRadix = fromInteger . natVal . logP . radixP

--

divByR :: (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, BitPack t) => T r t -> T r t
divByR x = flip floorDivByTwoToThePowerOf (logRadix x) <$> x

modR :: (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Algebra.Ring.C t, BitPack t) => T r t -> T r t
modR x = flip modulo (radixP x) <$> x

--

reduce1 :: (KnownNat p, Algebra.Ring.C t, Ord t) => T r t -> Proxy p -> T r t
x `reduce1` modP = if x < p then x else x - p where p = fromInteger (natVal modP)

reduce2 :: (KnownNat p, KnownNat q, KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Algebra.Ring.C t, BitPack t, Ord t) => T r t -> (Proxy p, Proxy q) -> T r t
x `reduce2` (modP, auxP) = x' `reduce1` modP where
  a = modR x
  b = a * fromInteger p'
  c = modR b
  d = x + c * fromInteger p
  x' = divByR d
  p' = natVal auxP
  p = natVal modP

instance (KnownNat p, KnownNat q, KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, Algebra.Ring.C t, Algebra.ToInteger.C t, BitPack t, Eq t, Ord t, Show t) => (PrimeField.C p q (T r t)) where
  x `into` (modP, _) = fromInteger $ x * natVal (Proxy :: Proxy r) `mod` natVal modP
  outfrom = (toInteger . decons) `compose2` reduce2 where compose2 = (.) . (.)
  (x, y) `addMod` (modP, _) = (x + y) `reduce1` modP
  (x, y) `mulMod` (modP, auxP)= (x * y) `reduce2` (modP, auxP) `reduce1` modP
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
