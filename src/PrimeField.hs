module PrimeField
  ( C(..)
  , T(..)
  , legendreSymbol
  , gen
  , genUnit
  ) where

import           Prelude             (Integral, (<$>))
import           Control.Applicative (Applicative(..))
import           Data.Bits           (Bits(..), FiniteBits(..))
import           Data.Proxy          (Proxy(..))
import           GHC.TypeLits        (KnownNat, natVal)

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.Field
import qualified Algebra.Ring
import qualified Algebra.ZeroTestable
import qualified MathObj.Wrapper.Haskell98 as W

import           Utils (foldrBits)

-- $

class (KnownNat p, KnownNat q, Algebra.Ring.C t, Eq t, FiniteBits t, Show t) => (C p q t) where
  into :: t -> (Proxy p, Proxy q) -> t
  outfrom :: t -> (Proxy p, Proxy q) -> t
  reduce1 :: t -> (Proxy p, Proxy q) -> t
  reduce2 :: t -> (Proxy p, Proxy q) -> t

--

instance (Applicative W.T) where
  pure = W.Cons
  liftA2 f (W.Cons x) (W.Cons y) = W.Cons $ f x y

instance (Bits t) => (Bits (W.T t)) where
  (.&.) = liftA2 (.&.)
  (.|.) = liftA2 (.|.)
  xor = liftA2 xor
  complement = fmap complement
  x `shift` i = flip shift i <$> x
  x `rotate` i = flip rotate i <$> x
  bitSize = bitSize . W.decons
  bitSizeMaybe = bitSizeMaybe . W.decons
  isSigned = isSigned . W.decons
  testBit = testBit . W.decons
  bit = W.Cons . bit
  popCount = popCount . W.decons

instance (FiniteBits t) => (FiniteBits (W.T t)) where
  finiteBitSize = finiteBitSize . W.decons

instance (KnownNat p, KnownNat q, Integral t, Eq t, FiniteBits t, Show t) => (C p q (W.T t)) where
  x `into` (modP, _) = x `mod` fromInteger (natVal modP)
  x `outfrom` _ = x
  reduce1 = into
  reduce2 = into

--

newtype T p q t = T t deriving (Eq, Functor, Show)

modulusPOf :: T p q t -> (Proxy p, Proxy q)
modulusPOf _ = (Proxy, Proxy)

modulusOf :: (KnownNat p, KnownNat q, Algebra.Ring.C t) => T p q t -> t
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

--

toThePowerOf :: (C p q t) => T p q t -> t -> T p q t
toThePowerOf x = foldrBits sm s 1 where
  sm = (x *) . s
  s = Algebra.Ring.sqr

instance (C p q t) => (Algebra.Field.C (T p q t)) where
  recip 0 = error "divide by zero"
  recip x = x `toThePowerOf` (modulusOf x - 2)

legendreSymbol :: (C p q t) => T p q t -> T p q t
legendreSymbol 0 = 0
legendreSymbol x = x `toThePowerOf` (modulusOf x `shiftR` 1)

--

gen :: (C p q t, H.MonadGen m) => (Proxy p, Proxy q) -> m (T p q t)
gen (modP, _) = do
  x <- Gen.integral $ Range.linear 0 (natVal modP - 1)
  return $ fromInteger x

genUnit :: (C p q t, H.MonadGen m) => (Proxy p, Proxy q) -> m (T p q t)
genUnit (modP, _) = do
  x <- Gen.integral $ Range.linear 1 (natVal modP - 1)
  return $ fromInteger x
