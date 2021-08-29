{-# LANGUAGE UndecidableInstances #-}

module PrimeField.MontgomeryN
  ( C
  , T
  , prop_fromIntegerIsHomomorphic
  , prop_homomorphism
  ) where

import           Prelude             (Integral)
import           Control.Applicative (Applicative(..))
import           Data.Bits           (Bits(..))
import           Data.Function       ((&))
import           Data.Proxy          (Proxy(..))
import           Data.Tuple          (swap)
import           GHC.TypeLits        (KnownNat, natVal)
import           GHC.TypeLits.Extra  (type CLog, FLog, Log)
import           GHC.TypeNats        (type (+), type (-), type (*), type (<=))

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.Laws
import qualified Algebra.Ring
import qualified Algebra.ToInteger
import qualified Algebra.ZeroTestable
import qualified MathObj.Wrapper.Haskell98 as W

import qualified Clash.Prelude as C
import qualified PrimeField
import           Radix2 (floorDivBy, modulo)
import           Utils  (composeN)

-- $

addVec1 :: forall n t. (KnownNat n, 1 <= n, Algebra.Additive.C t) => t -> C.Vec n t -> C.Vec n t
addVec1 x = C.zipWith ($) $ (x +) C.:> C.repeat @(n - 1) id

addVec :: forall n t. (KnownNat n, 1 <= n, Algebra.Additive.C t) => C.Vec n t -> C.Vec n t -> C.Vec n t
addVec = liftA2 (+)

multVec1 :: forall n t. (KnownNat n, 1 <= n, Algebra.Ring.C t) => t -> C.Vec n t -> C.Vec n t
multVec1 x = C.map (x *)

--

class (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, KnownNat n, 1 <= n, Algebra.ToInteger.C t, C.BitPack t, 2 * Log 2 r + 1 <= C.BitSize t, Eq t, Ord t, Show t) => (C r n t)

instance (KnownNat r, FLog 2 r ~ CLog 2 r, 2 <= r, KnownNat n, 1 <= n, Integral t, C.BitPack t, 2 * Log 2 r + 1 <= C.BitSize t, Eq t, Ord t, Show t) => (C r n (W.T t))

carryCanOverflow :: forall r n t. (C r n t) => C.Vec n t -> C.Vec n t
carryCanOverflow v = u C.:< acc + C.last @(n - 1) v where
  (acc, u) = C.mapAccumL f 0 $ C.init @(n - 1) v
  f x y = (x + y & floorDivBy @r, x + y & modulo @r)

carryModRToTheN :: forall r n t. (C r n t) => C.Vec n t -> C.Vec n t
carryModRToTheN = snd . C.mapAccumL f 0 where
  f x y = (x + y & floorDivBy @r, x + y & modulo @r)

--

newtype T r n t = Cons { decons :: C.Vec n t } deriving (Applicative, Eq, Functor, Show)

deriving instance (KnownNat n, C.NFDataX t) => (C.NFDataX (T r n t))

instance (C r n t) => (Algebra.ZeroTestable.C (T r n t)) where isZero = Algebra.ZeroTestable.defltIsZero

instance (C r n t) => (Algebra.Additive.C (T r n t)) where
  zero = pure 0
  Cons u + Cons v = Cons . carryCanOverflow @r $ u `addVec` v
  Cons u - s = Cons $ 1 `addVec1` u |+| (decons . C.unpack @(T r n t) . complement . C.pack) s where
    v1 |+| v2 = carryModRToTheN @r $ v1 `addVec` v2


instance (C r n t) => (Algebra.Ring.C (T r n t)) where
  (Cons u) * (Cons v) = C.foldr f 0 v where f x (Cons w) = Cons (multVec1 x u) + Cons (0 C.+>> w)
  fromInteger = Cons . C.map fromInteger . C.unfoldrI f where f = swap . flip divMod (natVal @r Proxy)

instance (C r n t) => (C.BitPack (T r n t)) where
  type BitSize (T r n t) = n * Log 2 r
  pack = C.pack . C.map (C.resize @_ @_ @(Log 2 r) . C.pack) . decons
  unpack = Cons . C.map (C.unpack . C.resize) . C.unpack @(C.Vec n (C.BitVector (Log 2 r)))

instance (C r n t) => (Ord (T r n t)) where
  (Cons u) `compare` (Cons v) = C.foldr f EQ $ C.zipWith compare u v where
    f x EQ = x
    f _ x = x

--

reduce1 :: forall p r n t. (KnownNat p, C r n t) => T r n t -> T r n t
reduce1 s = if s < p then s else s - p where p = fromInteger $ natVal @p Proxy

reduce2 :: forall p q r n t. (KnownNat p, KnownNat q, C r n t) => T r n t -> T r n t
reduce2 (Cons v) = reduce1 @p @r s where
  x = C.head @(n - 1) v & modulo @r
  y = x * fromInteger (natVal @q Proxy)
  z = y & modulo @r
  p = decons . fromInteger @(T r n t) $ natVal @p Proxy
  u = v `addVec` multVec1 z p
  lo = C.map (modulo @r) . (C.<<+ 0)
  hi = C.map (floorDivBy @r)
  s = Cons (lo u) + Cons (hi u)

instance (KnownNat p, 2 <= p , KnownNat q, C r n t) => (PrimeField.C p q (T r n t)) where
  into = fromInteger . composeN @n (flip mod (natVal @p Proxy) . (natVal @r Proxy *))
  outfrom = C.foldr f 0 . decons . composeN @n (reduce2 @p @q @r) where f x = (toInteger x +) . (natVal @r Proxy *)
  addMod = reduce1 @p @r `compose2` (+) where compose2 = (.) . (.)
  mulMod (Cons u) (Cons v) = C.foldl f 0 v where f (Cons w) x = (reduce2 @p @q @r @n) . Cons $ multVec1 x u `addVec` w
  invMod = PrimeField.fermatInverse @p @q

--

prop_fromIntegerIsHomomorphic
  :: forall r n t. (C r n t)
  => (Integer -> Integer -> Integer)
  -> (T r n t -> T r n t -> T r n t)
  -> Integer -> Integer -> Bool
prop_fromIntegerIsHomomorphic = Algebra.Laws.homomorphism fromInteger

prop_homomorphism
  :: forall p q r n t t'. (KnownNat p, 2 <= p, KnownNat q, C r n t, t' ~ W.T (C.Signed (1 + 2 * n * Log 2 r)))
  => (PrimeField.T p q t' -> PrimeField.T p q t' -> PrimeField.T p q t')
  -> (PrimeField.T p q (T r n t) -> PrimeField.T p q (T r n t) -> PrimeField.T p q (T r n t))
  -> PrimeField.T p q t' -> PrimeField.T p q t' -> Bool
prop_homomorphism = Algebra.Laws.homomorphism phi where
  phi = fmap $ PrimeField.into @p @q @(T r n t) . PrimeField.outfrom @p @q @t'
