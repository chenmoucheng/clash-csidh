module PrimeField.Montgomery1
  ( T(..)
  , prop_homomorphism
  ) where

import           Prelude             ((<$>))
import           Control.Applicative (Applicative(..))
import           Data.Bits           (Bits(..), FiniteBits(..))
import           Data.Proxy          (Proxy(..))
import           GHC.TypeLits        (KnownNat, natVal)
import           GHC.TypeLits.Extra  (type CLog)
import           GHC.TypeNats        (type (<=))

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.IntegralDomain
import qualified Algebra.Laws
import qualified Algebra.Ring

import qualified PrimeField
import           Utils (invMod)

-- $

newtype T r t = Cons { decons :: t } deriving (Eq, Functor, Show)

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

instance (Applicative (T r)) where
  pure = Cons
  liftA2 f (Cons x) (Cons y) = Cons $ f x y

instance (KnownNat r, 2 <= r, Algebra.Additive.C t, FiniteBits t) => (Algebra.Additive.C (T r t)) where
  zero = pure zero
  (+) = liftA2 (+)
  negate = fmap negate

instance (KnownNat r, 2 <= r, Algebra.Ring.C t, FiniteBits t) => (Algebra.Ring.C (T r t)) where
  (*) = liftA2 (*)
  fromInteger = pure . fromInteger

instance (Bits t) => (Bits (T r t)) where
  (.&.) = liftA2 (.&.)
  (.|.) = liftA2 (.|.)
  xor = liftA2 xor
  complement = fmap complement
  x `shift` i = flip shift i <$> x
  x `rotate` i = flip rotate i <$> x
  bitSize = bitSize . decons
  bitSizeMaybe = bitSizeMaybe . decons
  isSigned = isSigned . decons
  testBit = testBit . decons
  bit = Cons . bit
  popCount = popCount . decons

instance (FiniteBits t) => (FiniteBits (T r t)) where
  finiteBitSize = finiteBitSize . decons

--

instance (KnownNat p, KnownNat r, 2 <= r, Algebra.IntegralDomain.C t, Eq t, FiniteBits t, Ord t, Show t) => (PrimeField.C p (T r t)) where
  x `into` modP = Cons $ decons (multByR x) `mod` fromInteger (natVal modP)
  outfrom = PrimeField.reduce2
  (Cons x) `reduce1` modP = Cons $ if x < p then x else x - p where p = fromInteger (natVal modP)
  x `reduce2` modP = x' `PrimeField.reduce1` modP where
    a = modR x
    b = a * fromInteger p'
    c = modR b
    d = x + c * fromInteger p
    x' = divByR d
    p' = (-p) `invMod` radix x
    p = natVal modP

--

prop_homomorphism
  :: (PrimeField.C p t, PrimeField.C p (T r t))
  => Proxy p
  -> (PrimeField.T p (T r t) -> PrimeField.T p (T r t) -> PrimeField.T p (T r t))
  -> (PrimeField.T p t -> PrimeField.T p t -> PrimeField.T p t)
  -> PrimeField.T p (T r t) -> PrimeField.T p (T r t) -> Bool
prop_homomorphism modP = Algebra.Laws.homomorphism phi where
  phi (PrimeField.T x) = PrimeField.T $ decons (x `PrimeField.outfrom` modP) `PrimeField.into` modP
