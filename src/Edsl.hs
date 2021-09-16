module Edsl
  ( C(..)
  , share
  , shareEx
  , shareEx'
  , bram1Reader
  , bram1Writer
  )
  where

import           Data.Bifunctor (bimap)
import           Data.Coerce    (coerce)

import           NumericPrelude (ifThenElse)

import           Clash.Prelude
import           Protocols (Circuit(..), Df, Fwd, (<|), repeatC)
import qualified Protocols.Df as Df

import           ExeUnit (hasPayload)

-- $

class C f where
  type ClockDomain f :: Domain
  bundleVecC   :: (HiddenClockResetEnable (ClockDomain f), KnownNat n, 1 <= n, NFDataX a) => Circuit (Vec n (f a)) (f (Vec n a))
  fanoutC      :: (HiddenClockResetEnable (ClockDomain f), KnownNat n, 1 <= n) => Circuit (f a) (Vec n (f a))
  mapC         :: (a -> b) -> Circuit (f a) (f b)
  partitionC   :: (a -> Bool) -> Circuit (f a) (f a, f a)
  pureC        :: Df.Data a -> Circuit () (f a)
  registerBwdC :: (HiddenClockResetEnable (ClockDomain f), NFDataX a) => Circuit (f a) (f a)
  registerFwdC :: (HiddenClockResetEnable (ClockDomain f), NFDataX a) => Circuit (f a) (f a)
  routeC       :: (KnownNat n) => Circuit (f (Index n, a)) (Vec n (f a))
  selectC      :: (KnownNat n) => Circuit (Vec n (f a), f (Index n)) (f a)
  unbundleVecC :: (HiddenClockResetEnable (ClockDomain f), KnownNat n, 1 <= n, NFDataX a) => Circuit (f (Vec n a)) (Vec n (f a))
  zipC         :: Circuit (f a, f b) (f (a, b))

  foldlC       :: (HiddenClockResetEnable (ClockDomain f), KnownNat n, 1 <= n, NFDataX a, NFDataX b) => Circuit (f (b, a)) (f b) -> Circuit (Vec n (f a), f b) (f b)
  foldrC       :: (HiddenClockResetEnable (ClockDomain f), KnownNat n, 1 <= n, NFDataX a, NFDataX b) => Circuit (f (a, b)) (f b) -> Circuit (Vec n (f a), f b) (f b)
  untilC       :: (HiddenClockResetEnable (ClockDomain f), NFDataX a) => (a -> Bool) -> Circuit (f a) (f a) -> Circuit (f a) (f a)

--

instance C (Df dom) where
  type ClockDomain (Df dom) = dom
  bundleVecC   = Df.bundleVec
  fanoutC      = Df.fanout
  mapC         = Df.map
  partitionC   = Df.partition
  pureC        = Df.pure
  registerBwdC = Df.registerBwd
  registerFwdC = Df.registerFwd
  routeC       = Df.route
  selectC      = Df.select
  unbundleVecC = Df.unbundleVec
  zipC         = Df.zip

--

  foldlC
    :: forall n a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a, NFDataX b)
    => Circuit (Df dom (b, a)) (Df dom b)
    -> Circuit (Vec n (Df dom a), Df dom b) (Df dom b)
  foldlC cir = circuit $ \(xs, y0) -> do
    -- zipVecC :: Circuit (Vec n (Df dom a), Vec n (Df dom b)) (Vec n (Df dom a, Df dom b))
    let zipVecC = Circuit $ \((iDats1, iDats2), iAcks) -> (unzip iAcks, zip iDats1 iDats2)
    toShared <- repeatC zipC  <| zipVecC -< (fb, xs)
    fromShared <- share cir -< toShared
    -- feedbackC :: Circuit (Df dom a, Vec n (Df dom a)) (Vec n (Df dom a), Df dom a)
    let feedbackC = Circuit $ \((iDat, iDats), (iAcks, iAck)) -> ((head @(n - 1) iAcks, iAcks <<+ iAck), (iDat +>> iDats, last @(n - 1) iDats))
    (fb, yn) <- feedbackC -< (y0, fromShared)
    idC -< yn

  foldrC
    :: forall n a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a, NFDataX b)
    => Circuit (Df dom (a, b)) (Df dom b)
    -> Circuit (Vec n (Df dom a), Df dom b) (Df dom b)
  foldrC cir = circuit $ \(xs, yn) -> do
    -- zipVecC :: Circuit (Vec n (Df dom a), Vec n (Df dom b)) (Vec n (Df dom a, Df dom b))
    let zipVecC = Circuit $ \((iDats1, iDats2), iAcks) -> (unzip iAcks, zip iDats1 iDats2)
    toShared <- repeatC zipC  <| zipVecC -< (xs, fb)
    fromShared <- share cir -< toShared
    -- feedbackC :: Circuit (Vec n (Df dom a), Df dom a) (Df dom a, Vec n (Df dom a))
    let feedbackC = Circuit $ \((iDats, iDat), (iAck, iAcks)) -> ((iAck +>> iAcks, last @(n - 1) iAcks), (head @(n - 1) iDats, iDats <<+ iDat))
    (y0, fb) <- feedbackC -< (fromShared, yn)
    idC -< y0

  untilC cond loop = circuit $ \a -> do
    b <- registerBwdC <| selectC -< ([a, f], i)
    (c, d) <- partitionC cond -< b
    let go x = if hasPayload x then pure 1 else pure 0
    (e, i) <- peek $ fmap go -< d
    f <- loop -< e
    idC -< c

--

peek
  :: (HiddenClockResetEnable dom, NFDataX b)
  => (Fwd a -> Fwd (Df dom b))
  -> Circuit a (a, Df dom b)
peek f = Circuit $ \(iDat, (iAck, ack)) -> let
  dat = f iDat
  sel = moore go id True $ bundle (hasPayload <$> dat, coerce <$> ack) where
    go True  (True, False) = False
    go False (_,     True) = True
    go s _ = s
  in (iAck, (iDat, mux sel dat $ register empty dat))

share
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Df dom a) (Df dom b)
  -> Circuit (Vec n (Df dom a)) (Vec n (Df dom b))
share cir = circuit $ \xs -> do
  fromShared <- cir -< toShared
  (toShared, ys) <- shareEx registerFwdC -< (xs, fromShared)
  idC -< ys

shareEx
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Df dom (Index n)) (Df dom (Index n))
  -> Circuit (Vec n (Df dom a), Df dom b) (Df dom a, Vec n (Df dom b))
shareEx buf = circuit $ \(xs, fromShared) -> do
  let selC = peek $ fmap (maybe empty pure . findIndex hasPayload) . bundle
  (ys, i) <- selC -< xs
  [j, k] <- fanoutC -< i
  toShared <- selectC -< (ys, j)
  l <- buf -< k
  zs <- routeC <| zipC -< (l, fromShared)
  idC -< (toShared, zs)

shareEx'
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Vec n (Df dom a)) (Df dom a)
shareEx' = circuit $ \xs -> do
  let selC = peek $ fmap (maybe empty pure . findIndex hasPayload) . bundle
  toShared <- selectC <| selC -< xs
  idC -< toShared
--

bram1Reader
  :: (HiddenClockResetEnable dom, BitPack a, NFDataX a, KnownNat n, 1 <= n, BitPack t, NFDataX t, KnownNat m, 1 <= m, (m * BitSize a) ~ BitSize t)
  => Circuit (Df dom a) (Df dom a)
  -> Circuit (Df dom (Unsigned n), Df dom a) (Df dom (Unsigned n), Df dom t)
bram1Reader buf = circuit $ \(addr, fromBram) -> do
  addrs <- unbundleVecC <| mapC (iterateI (1 +)) -< addr
  (toBram, douts) <- shareEx registerFwdC -< (addrs, fromBram)
  dout <- mapC unpack <| mapC pack <| bundleVecC <| repeatC buf -< douts
  idC -< (toBram, dout)

bram1Writer
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, BitPack a, NFDataX a, BitPack t, NFDataX t, KnownNat m, 1 <= m, (m * BitSize a) ~ BitSize t)
  => Circuit (Df dom (Unsigned n, t)) (Df dom (Unsigned n, a))
bram1Writer = circuit $ \din -> do
  let f = iterateI (1 +)
  let g = unpack . pack
  dins <- unbundleVecC <| mapC (uncurry zip . bimap f g) -< din
  toBram <- shareEx' -< dins
  idC -< toBram
