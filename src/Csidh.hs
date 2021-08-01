module Csidh
  ( K
  , P
  , Prvkey
  , Scalar
  , action
  , ells
  , genkey
  , genkey2
  , ellTorsionPoint
  , prop_scalarMultiplicationIsHomomorphic
  , prop_groupActionCommutesWithScalarMultiplication
  , prop_groupActionIsCommutative
  ) where

import           Prelude      ()
import           Data.Bits    (FiniteBits)
import           GHC.TypeLits (KnownNat)

import qualified Hedgehog as H
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           NumericPrelude
import qualified Algebra.Ring
import qualified MathObj.Wrapper.Haskell98 as W

import           Clash.Prelude (Vec((:>)))
import qualified Clash.Prelude as C
import qualified PrimeField
import           Isogeny

-- $

type CsidhVec = C.Vec 74
type Scalar = W.T (C.Unsigned 10)

ells :: CsidhVec Scalar
ells =
    3 :> 5 :> 7 :> 11 :> 13 :> 17 :> 19 :> 23 :> 29 :> 31 :> 37 :> 41 :> 43 :> 47 :> 53 :> 59 :> 61 :> 67 :> 71 :>
    73 :> 79 :> 83 :> 89 :> 97 :> 101 :> 103 :> 107 :> 109 :> 113 :> 127 :> 131 :> 137 :> 139 :> 149 :> 151 :> 157 :>
    163 :> 167 :> 173 :> 179 :> 181 :> 191 :> 193 :> 197 :> 199 :> 211 :> 223 :> 227 :> 229 :> 233 :> 239 :> 241 :>
    251 :> 257 :> 263 :> 269 :> 271 :> 277 :> 281 :> 283 :> 293 :> 307 :> 311 :> 313 :> 317 :> 331 :> 337 :> 347 :>
    349 :> 353 :> 359 :> 367 :> 373 :> 587 :> C.Nil

type Prvkey = CsidhVec (W.T (C.Signed 4))
type P = 5326738796327623094747867617954605554069371494832722337612446642054009560026576537626892113026381253624626941643949444792662881241621373288942880288065659
type K q t = PrimeField.T P q t

--

vectorMultiplicationWithCofactor
  :: (KnownNat n, Algebra.Ring.C t, FiniteBits t, Algebra.Ring.C k, Eq k)
  => (C.Vec n t, k, k, k, t) -> (k, k)
vectorMultiplicationWithCofactor (ns, x, z, a, c) = C.foldl f (x0, z0) ns where
  (x0, z0) = scalarMultiplicationMontgomeryPlus (c, x, z, a)
  f (_x, _z) n = scalarMultiplicationMontgomeryPlus (n, _x, _z, a)

replaceWith :: (KnownNat n) => (a -> Bool) -> a -> C.Vec n a -> C.Vec n a
replaceWith cond x xs = fmap (\_x -> if cond _x then x else _x) xs

ellTorsionPoint :: (PrimeField.C P q t) => (Scalar, K q t, K q t, K q t) -> (K q t, K q t)
ellTorsionPoint (ell, x, z, a) = vectorMultiplicationWithCofactor (replaceWith (ell ==) 1 ells, x, z, a, 4)

--

action1 :: (PrimeField.C P q t) => (Prvkey, K q t, K q t) -> (Prvkey, K q t)
action1 (sk, a, xP) = (sk', a'*t) where
  t = PrimeField.legendreSymbol $ xP^3 + a*xP^2 + xP
  twist = case t of
    1 -> 1
    0 -> 0
    _ -> -1
  ells' = snd . C.unzip . replaceWith ((0 <) . (twist *) . fst) (0, 1) $ C.zip sk ells
  (xQ, zQ) = vectorMultiplicationWithCofactor (ells', xP*t, 1, a*t, 4)
  (_, _, a', sk', _) = until f g (xQ, zQ, a*t, sk, 0) where
    f (_, 0, _, _, _) = True
    f (_, _, _, _, i) = i >= length sk
    g (_xQ, _zQ, _a, _sk, i)
      | (sk C.!! i) * twist > 0 = let
        ell = ells C.!! i
        (xR, zR) = vectorMultiplicationWithCofactor (replaceWith (ell ==) 1 ells', _xQ / _zQ, 1, _a, 4)
        ((_a', _xQ', _zQ'), _sk') = case zR of
          0 -> ((_a, _xQ, _zQ), _sk)
          _ -> (actWithEllOnMontgomeryPlus (_a, ell, xR / zR, _xQ / _zQ), C.replace i ((sk C.!! i) - twist) _sk)
        in (_xQ', _zQ', _a', _sk', i + 1)
      | otherwise = (_xQ, _zQ, _a, _sk, i + 1)

action :: (PrimeField.C P q t, KnownNat n) => (Prvkey, K q t, C.Vec n (K q t)) -> K q t
action (sk, a, xPs) = a' where
  ((_, a'), _) = until f g ((sk, a), 0) where
    f ((_sk, _), i)
      | i >= C.length xPs = error "supply of random points exhausted"
      | otherwise = C.foldl (\x y -> x && (y == 0)) True _sk
    g ((_sk, _a), i) = (action1 (_sk, _a, xPs C.!! i), i + 1)

--

genkey :: (H.MonadGen m) => m Prvkey
genkey = do
  let g = Gen.integral $ Range.linear (-5) 5
  xs <- Gen.list (Range.singleton $ length ells) g
  return $ C.unfoldrI (\(x:_xs) -> (x, _xs)) xs

genkey2 :: (H.MonadGen m) => m Prvkey
genkey2 = do
  i <- Gen.integral $ Range.linear 0 (length ells - 1)
  j <- Gen.integral $ Range.linear 0 (length ells - 1)
  return . C.replace i 1 . C.replace j (-1) $ C.repeat 0

--

prop_groupActionIsCommutative :: (KnownNat n, PrimeField.C P q t) => Prvkey -> Prvkey -> C.Vec n (K q t) -> Bool
prop_groupActionIsCommutative skA skB xPs = action (skA, pkB, xPs) == action (skB, pkA, xPs) where
    pkA = action (skA, 0, xPs)
    pkB = action (skB, 0, xPs)
