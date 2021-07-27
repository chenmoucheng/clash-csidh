{-# LANGUAGE RebindableSyntax #-}

module Csidh.Lib where

import           Prelude   ()
import           Data.Bits (Bits(..), FiniteBits(..))

import           NumericPrelude hiding (pi)
import qualified Algebra.Field
import qualified Algebra.Laws
import qualified Algebra.Ring

import           Utils (EvalEndofunc(..), Ratio(..), compose, foldrBits)

--

stepZeroMontgomeryPlus :: (Algebra.Ring.C t) => (t, t, t, t, t, t, t) -> (t, t, t, t, t, t, t)
stepZeroMontgomeryPlus (x1, z1, x2, z2, x3, z3, a) = (x1, z1, (x2^2 - z2^2)^2, 4*x2*z2*(x2^2 + a*x2*z2 + z2^2), 4*(x2*x3 - z2*z3)^2*z1, 4*(x2*z3 - z2*x3)^2*x1, a)

stepOneMontgomeryPlus :: (Algebra.Ring.C t) => (t, t, t, t, t, t, t) -> (t, t, t, t, t, t, t)
stepOneMontgomeryPlus (x1, z1, x3, z3, x2, z2, a) = (x1, z1, 4*(x2*x3 - z2*z3)^2*z1, 4*(x2*z3 - z2*x3)^2*x1, (x2^2 - z2^2)^2, 4*x2*z2*(x2^2 + a*x2*z2+z2^2), a)

scalarMultiplicationMontgomeryPlus :: (Algebra.Ring.C t, FiniteBits t, Algebra.Ring.C k, Eq k) => (t, k, k, k) -> (k, k)
scalarMultiplicationMontgomeryPlus (_, _, 0, _) = (1, 0)
scalarMultiplicationMontgomeryPlus (1, x, z, _) = (x, z)
scalarMultiplicationMontgomeryPlus (n, x1, z1, a) = (x2, z2) where
    (_, _, x2, z2, _, _, _) = foldrBits stepOneMontgomeryPlus stepZeroMontgomeryPlus (x1, z1, 1, 0, x1, z1, a) n

--

differentialAdditionMontgomeryPlus :: (Algebra.Ring.C t, Eq t) => (t, t, t, t, t, t, t) -> (t, t)
differentialAdditionMontgomeryPlus (0, _, _, _, _, _, _) = (0, 0)
differentialAdditionMontgomeryPlus (_, 0, _, _, _, _, _) = (0, 0)
differentialAdditionMontgomeryPlus (_, _, 0, 0, _, _, _) = (0, 0)
differentialAdditionMontgomeryPlus (_, _, _, _, 0, 0, _) = (0, 0)
differentialAdditionMontgomeryPlus (x1, z1, x2, z2, x3, z3, _) = (4*(x2*x3 - z2*z3)^2*z1, 4*(x2*z3 - z2*x3)^2*x1)

doublePointMontgomeryPlus :: (Algebra.Ring.C t, Eq t) => (t, t, t) -> (t, t)
doublePointMontgomeryPlus (_, 0, _) = (0, 0)
doublePointMontgomeryPlus (x2, z2, a)
    | x2^3 + a*x2^2 + x2 == 0 = (0, 0)
    | otherwise = ((x2^2 - z2^2)^2, 4*x2*z2*(x2^2 + a*x2*z2 + z2^2))

actWithEllOnMontgomeryPlus :: (Algebra.Field.C k, Eq k, Algebra.Ring.C t, Eq t, FiniteBits t, Ord t) => (k, t, k, k) -> (k, k, k)
actWithEllOnMontgomeryPlus (a, ell, xTors, xPush)
    | ell == 3  = ( pi^2*(a - 6* sigma),  fXPush,  fZPush)
    | otherwise = (_pi^2*(a - 6*_sigma), _fXPush, _fZPush)
    where
        xQ = xTors
        zQ = 1
        pi = xQ
        sigma = xQ - recip xQ
        fXPush = xPush*(xQ*xPush - 1)^2
        fZPush = (xPush - xQ)^2

        (xQ', zQ') = doublePointMontgomeryPlus (xQ, zQ, a)
        (pi', sigma', fXPush', fZPush') = f (xQ' / zQ') (pi, sigma, fXPush, fZPush)
        f xq (_pi, _sigma, _fXPush, _fZPush) = (_pi', _sigma', _fXPush', _fZPush') where
            _pi' = _pi*xq
            _sigma' = _sigma + (xq - recip xq)
            _fXPush' = _fXPush*(xq*xPush - 1)^2
            _fZPush' = _fZPush*(xPush - xq)^2

        (_, _, _pi, _sigma, _fXPush, _fZPush, _, _, _) = until g h (xQ', zQ', pi', sigma', fXPush', fZPush', xTors, 1, 3)
        g (_, _, _, _, _, _, _, _, i) = i > ell `shiftR` 1
        h (_xQ, _zQ, _pi, _sigma, _fXPush, _fZPush, xPrev, zPrev, i) = (_xQ', _zQ', _pi', _sigma', _fXPush', _fZPush', _xQ, _zQ, i + 1) where
            (_xQ', _zQ') = differentialAdditionMontgomeryPlus (xPrev, zPrev, xTors, 1, _xQ, _zQ, a)
            (_pi', _sigma', _fXPush', _fZPush') = f (_xQ' / _zQ') (_pi, _sigma, _fXPush, _fZPush)

--

prop_scalarMultiplicationIsHomomorphic :: (Algebra.Ring.C t, FiniteBits t, Algebra.Ring.C k, Eq k) => t -> t -> k -> k -> Bool
prop_scalarMultiplicationIsHomomorphic n m x z = Algebra.Laws.homomorphism phi (*) compose n m where
    f _n (R _x _z) = R _x' _z' where (_x', _z') = scalarMultiplicationMontgomeryPlus (_n, _x, _z, 0)
    phi _n = E (f _n) (R x z)

prop_groupActionCommutesWithScalarMultiplication :: (Algebra.Ring.C t, Eq t, FiniteBits t, Ord t, Algebra.Field.C k, Eq k) => t -> k -> t -> k-> Bool
prop_groupActionCommutesWithScalarMultiplication ell xTor n x = Algebra.Laws.commutative compose (E f (0, R x 1)) (E g (0, R x 1)) where
    f (_a, R _x _z) = (_a', R _x' _z') where (_a', _x', _z') = actWithEllOnMontgomeryPlus (_a, ell, xTor, _x / _z)
    g (_a, R _x _z) = (_a,  R _x' _z') where (_x', _z') = scalarMultiplicationMontgomeryPlus (n, _x, _z, _a)
