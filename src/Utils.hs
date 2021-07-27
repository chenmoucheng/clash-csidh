{-# LANGUAGE RebindableSyntax #-}

module Utils where

import           Prelude   ()
import           Data.Bits (Bits(..), FiniteBits(..))

import           NumericPrelude
import qualified Algebra.Ring

--

data Ratio t = R t t deriving (Show)
instance (Algebra.Ring.C t, Eq t) => (Eq (Ratio t)) where
  R x1 z1 == R x2 z2 = x1 * z2 == x2 * z1

data EvalEndofunc t = E (t -> t) t
instance (Eq t) => (Eq (EvalEndofunc t)) where
  E f x == E g y = f x == g y

compose :: (Eq t) => EvalEndofunc t -> EvalEndofunc t -> EvalEndofunc t
compose (E f x) (E g y)
  | x == y = E (f . g) x
  | otherwise = error "cannot compose endofunctions evaluated at different inputs"

--

foldlBits :: (FiniteBits i) => (a -> a) -> (a -> a) -> a -> i -> a
foldlBits t f z bv
  | bv == zeroBits = z
  | otherwise = foldlBits t f (if testBit bv 0 then t z else f z) $ bv `shiftR` 1

foldrBits :: (FiniteBits i) => (a -> a) -> (a -> a) -> a -> i -> a
foldrBits t f z bv = fst $ until g h (z, finiteBitSize bv - 1 - countLeadingZeros bv) where
  g (_, i) = i < 0
  h (x, i) = (if testBit bv i then t x else f x, i - 1)
