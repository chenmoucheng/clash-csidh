{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax      #-}

module PrimeField
  ( C (..)
  , T
  , gen
  , genUnit
  ) where

import qualified Prelude as P
import           Control.Applicative (Applicative(..), (<$>))
import           Data.Bits           (Bits(..), FiniteBits(..))
import           Data.Proxy          (Proxy(..))
import           GHC.TypeLits        (KnownNat, Nat, natVal)

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified Algebra.Additive
import qualified Algebra.Field
import qualified Algebra.Ring
import qualified Algebra.ZeroTestable
import qualified MathObj.Wrapper.Haskell98 as W

--

class (KnownNat p, Algebra.Ring.C t) => (C (p :: Nat) t) where
  into :: t -> Proxy p -> t
  outfrom :: t -> Proxy p -> t
  reduce1 :: t -> Proxy p -> t
  reduce2 :: t -> Proxy p -> t

--

instance (KnownNat p, P.Integral t) => (C p (W.T t)) where
  x `into` modP = x `mod` fromInteger (natVal modP)
  x `outfrom` _ = x
  reduce1 = into
  reduce2 = into

instance (Applicative W.T) where
  pure = W.Cons
  liftA2 f (W.Cons x) (W.Cons y) = W.Cons $ f x y

instance (Bits t) => (Bits (W.T t)) where
  (.&.) = liftA2 (.&.)
  (.|.) = liftA2 (.|.)
  xor = liftA2 xor
  complement = fmap complement
  shift x i = flip shift i <$> x
  rotate x i = flip rotate i <$> x
  bitSize = bitSize . W.decons
  bitSizeMaybe = bitSizeMaybe . W.decons
  isSigned = isSigned . W.decons
  testBit = testBit . W.decons
  bit = W.Cons . bit
  popCount = popCount . W.decons

instance (FiniteBits t) => (FiniteBits (W.T t)) where
  finiteBitSize = finiteBitSize . W.decons

--

newtype T p t = T t deriving (Eq, Functor, Show)

modulusPOf :: T p t -> Proxy p
modulusPOf _ = Proxy

modulusOf :: (KnownNat p, Algebra.Ring.C t) => T p t -> t
modulusOf = fromInteger . natVal . modulusPOf

--

instance (C p t, Algebra.Additive.C t, Eq t) => (Algebra.ZeroTestable.C (T p t)) where
  isZero = Algebra.ZeroTestable.defltIsZero

instance (C p t, Algebra.Additive.C t) => (Algebra.Additive.C (T p t)) where
  zero = T zero
  (T x) + (T y) = let z = T $ (x + y) `reduce1` modulusPOf z in z
  negate (T x) = let z = T $ modulusOf z - x in z

instance (C p t, Algebra.Ring.C t) => (Algebra.Ring.C (T p t)) where
  (T x) * (T y) = let z = T $ (x * y) `reduce2` modulusPOf z in z
  fromInteger i
    | i < 0 = negate . fromInteger $ -i
    | otherwise = let z = T $ fromInteger i `into` modulusPOf z in z

--

foldrBits :: (FiniteBits i) => (a -> a) -> (a -> a) -> a -> i -> a
foldrBits t f x bv = fst $ until g h (x, finiteBitSize bv - 1 - countLeadingZeros bv) where
  g (_, i) = i < 0
  h (y, i) = (if testBit bv i then t y else f y, i - 1)

toThePowerOf :: (C p t, Algebra.Ring.C t, FiniteBits t) => T p t -> t -> T p t
toThePowerOf x = foldrBits sm s one where
  sm = (x *) . s
  s = Algebra.Ring.sqr

instance (C p t, Algebra.Ring.C t, Eq t, FiniteBits t) => (Algebra.Field.C (T p t)) where
  recip 0 = error "divide by zero"
  recip x = x `toThePowerOf` (modulusOf x - 2)

--

gen :: (KnownNat p, C p t, Algebra.Ring.C t, H.MonadGen m) => Proxy p -> m (T p t)
gen modP = do
  x <- Gen.integral $ Range.linear 0 (natVal modP - 1)
  return $ fromInteger x

genUnit :: (KnownNat p, C p t, Algebra.Ring.C t, H.MonadGen m) => Proxy p -> m (T p t)
genUnit modP = do
  x <- Gen.integral $ Range.linear 1 (natVal modP - 1)
  return $ fromInteger x
