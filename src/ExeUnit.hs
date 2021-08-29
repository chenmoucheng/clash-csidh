{-# LANGUAGE DeriveAnyClass #-}

module ExeUnit
  ( dsp48mult
  , mkExeUnit
  , mkBram1
  , mkBram2
  , bram1Reader
  , bram1Writer
  , share
  , shareEx
  , shareEx'
  , foldlC
  , foldrC
  , untilC
  , toData
  , fromData
  ) where

import           Data.Bifunctor               (bimap, first)
import           Data.Coerce                  (coerce)
import           Data.Proxy                   (Proxy(..))
import           Data.String.Interpolate      (i)
import           Data.String.Interpolate.Util (unindent)

import           NumericPrelude (ifThenElse)

import           Clash.Annotations.Primitive (HDL(..), Primitive(..))
import           Clash.Prelude
import           Protocols (Circuit(..), Df, Protocol(..), (<|), (|>), repeatC, toSignals)
import qualified Protocols.Df as Df

-- $

{-# ANN (|*|#) (InlinePrimitive [Verilog] $ unindent [i|
  [ { "BlackBox" :
      { "name" : "ExeUnit.|*|#"
      , "kind" : "Expression"
      , "type" : "(|*|#) :: (KnownNat m, KnownNat n) => BitVector m -> BitVector m -> BitVector n"
      , "template" : "~ARG[2]  *  ~ARG[3]"
      }
    }
  ]
  |]) #-}
(|*|#) :: forall m n. (KnownNat m, KnownNat n) => BitVector m -> BitVector m -> BitVector n
(|*|#) x y = pack $ x' * y' where
  x' = unpack @(Signed n) $ resize x
  y' = unpack @(Signed n) $ resize y
{-# NOINLINE (|*|#) #-}

dsp48mult :: forall n t. (KnownNat n, BitPack t) => t -> t -> t
dsp48mult x y = unpack $ x' |*|# y' where
  x' = resize @_ @_ @n $ pack x
  y' = resize @_ @_ @n $ pack y

--

data State (n :: Nat) = Idle | Busy (Index n) | Wait deriving (Eq, Show)
deriving instance (KnownNat n, 1 <= n) => Generic (State n)
deriving instance (KnownNat n, 1 <= n) => NFDataX (State n)
deriving instance (KnownNat n, 1 <= n) => ShowX (State n)

entryState :: forall n. (KnownNat n, 1 <= n) => State n
entryState = Busy . fromInteger $ natVal @(n - 1) Proxy

mkFSM
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => (Fwd (Df dom a), Bwd (Df dom b))
  -> Signal dom (State n, State n)
mkFSM = mealy go Idle . bundle where
  go s (dat, ack) = (s', (s, s')) where
    s' = case (s, hasPayload dat, coerce ack) of
      (Idle,    True,     _) -> entryState
      (Busy 0,  True,  True) -> entryState
      (Busy 0, False,  True) -> Idle
      (Busy 0,     _, False) -> Wait
      (Busy x,     _,     _) -> Busy (x - 1)
      (Wait,    True,  True) -> entryState
      (Wait,   False,  True) -> Idle
      (state,      _,     _) -> state

poseData :: (KnownNat n, 1 <= n) => (State n, State n) -> Bool
poseData (s, _) = s == Wait || s == Busy 0

poseAck :: (KnownNat n, 1 <= n) => (a, State n) -> Bool
poseAck (_, s) = s == entryState

canEn :: (State n, State n) -> Bool
canEn (snd -> Busy _) = True
canEn _ = False

--

mkExeUnit
  :: forall dom n a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => (Enable dom -> Signal dom a -> Signal dom b)
  -> Circuit (Df dom a) (Df dom b)
mkExeUnit f = Circuit . hideEnable $ \en (iDat, iAck) -> let
  s = mkFSM @dom @n (iDat, iAck)
  oAck = coerce . poseAck <$> s
  en' = toEnable $ fromEnable en .&&. canEn <$> s
  fout = f en' (getPayloadUnsafe <$> iDat)
  oDat = toData <$> bundle (poseData <$> s, fout)
  in (oAck, oDat)

--

mkBram1
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => Vec (2 ^ n) a
  -> Circuit (Df dom (Unsigned n, Maybe (Unsigned n, a))) (Df dom a)
mkBram1 contents = mkExeUnit @_ @1 f where
  -- to avoid monomorphism restriction
  f x = (exposeEnable $ uncurry (readNew $ blockRamPow2 contents) . unbundle) x

mkBram2
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => Vec (2 ^ n) a
  -> Circuit (Df dom (Unsigned n), Df dom (Unsigned n, a)) (Df dom a)
mkBram2 contents = Circuit $ \((iRdDat, iWrDat), iAck) -> let
  adpt = Circuit $ first unbundle . unbundle . fmap go . bundle . first bundle where
    -- go :: ((Df.Data a, Df.Data b), Df.Ack (a, Maybe b)) -> ((Df.Ack a, Df.Ack b), Df.Data (a, Maybe b))
    go ((Df.Data x, Df.Data y), ack) = ((coerce ack, coerce ack), pure (x, Just y))
    go ((Df.Data x, Df.NoData), ack) = ((coerce ack, coerce False), pure (x, Nothing))
    go ((Df.NoData, Df.Data y), ack) = ((coerce False, coerce ack), pure (undefined, Just y))
    go _ = ((coerce False, coerce False), empty)
  wrOnly = register False $ (not . hasPayload <$> iRdDat) .&&. hasPayload <$> iWrDat
  ((oRdAck, oWrAck), oDat) = toSignals (adpt |> mkBram1 contents) ((iRdDat, iWrDat), coerce $ coerce iAck .||. wrOnly)
  in ((oRdAck, oWrAck), oDat)

--

bram1Reader
  :: (HiddenClockResetEnable dom, BitPack a, NFDataX a, KnownNat n, 1 <= n, BitPack t, NFDataX t, KnownNat m, 1 <= m, (m * BitSize a) ~ BitSize t)
  => Circuit (Df dom a) (Df dom a)
  -> Circuit (Df dom (Unsigned n), Df dom a) (Df dom (Unsigned n), Df dom t)
bram1Reader buf = circuit $ \(addr, fromBram) -> do
  addrs <- Df.unbundleVec <| Df.map (iterateI (1 +)) -< addr
  (toBram, douts) <- shareEx Df.registerFwd -< (addrs, fromBram)
  dout <- Df.map unpack <| Df.map pack <| Df.bundleVec <| repeatC buf -< douts
  idC -< (toBram, dout)

bram1Writer
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, BitPack a, NFDataX a, BitPack t, NFDataX t, KnownNat m, 1 <= m, (m * BitSize a) ~ BitSize t)
  => Circuit (Df dom (Unsigned n, t)) (Df dom (Unsigned n, a))
bram1Writer = circuit $ \din -> do
  let f = iterateI (1 +)
  let g = unpack . pack
  dins <- Df.unbundleVec <| Df.map (uncurry zip . bimap f g) -< din
  toBram <- shareEx' -< dins
  idC -< toBram

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
  (toShared, ys) <- shareEx Df.registerFwd -< (xs, fromShared)
  idC -< ys

shareEx
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Df dom (Index n)) (Df dom (Index n))
  -> Circuit (Vec n (Df dom a), Df dom b) (Df dom a, Vec n (Df dom b))
shareEx buf = circuit $ \(xs, fromShared) -> do
  let selC = peek $ fmap (maybe empty pure . findIndex hasPayload) . bundle
  (ys, i) <- selC -< xs
  [j, k] <- Df.fanout -< i
  toShared <- Df.select -< (ys, j)
  l <- buf -< k
  zs <- Df.route <| Df.zip -< (l, fromShared)
  idC -< (toShared, zs)

shareEx'
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Vec n (Df dom a)) (Df dom a)
shareEx' = circuit $ \xs -> do
  let selC = peek $ fmap (maybe empty pure . findIndex hasPayload) . bundle
  toShared <- Df.select <| selC -< xs
  idC -< toShared

--

foldlC
  :: forall dom n a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a, NFDataX b)
  => Circuit (Df dom (b, a)) (Df dom b)
  -> Circuit (Vec n (Df dom a), Df dom b) (Df dom b)
foldlC cir = circuit $ \(xs, y0) -> do
  -- zipVecC :: Circuit (Vec n (Df dom a), Vec n (Df dom b)) (Vec n (Df dom a, Df dom b))
  let zipVecC = Circuit $ \((iDats1, iDats2), iAcks) -> (unzip iAcks, zip iDats1 iDats2)
  toShared <- repeatC Df.zip  <| zipVecC -< (fb, xs)
  fromShared <- share cir -< toShared
  -- feedbackC :: Circuit (Df dom a, Vec n (Df dom a)) (Vec n (Df dom a), Df dom a)
  let feedbackC = Circuit $ \((iDat, iDats), (iAcks, iAck)) -> ((head @(n - 1) iAcks, iAcks <<+ iAck), (iDat +>> iDats, last @(n - 1) iDats))
  (fb, yn) <- feedbackC -< (y0, fromShared)
  idC -< yn

foldrC
  :: forall dom n a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a, NFDataX b)
  => Circuit (Df dom (a, b)) (Df dom b)
  -> Circuit (Vec n (Df dom a), Df dom b) (Df dom b)
foldrC cir = circuit $ \(xs, yn) -> do
  -- zipVecC :: Circuit (Vec n (Df dom a), Vec n (Df dom b)) (Vec n (Df dom a, Df dom b))
  let zipVecC = Circuit $ \((iDats1, iDats2), iAcks) -> (unzip iAcks, zip iDats1 iDats2)
  toShared <- repeatC Df.zip  <| zipVecC -< (xs, fb)
  fromShared <- share cir -< toShared
  -- feedbackC :: Circuit (Vec n (Df dom a), Df dom a) (Df dom a, Vec n (Df dom a))
  let feedbackC = Circuit $ \((iDats, iDat), (iAck, iAcks)) -> ((iAck +>> iAcks, last @(n - 1) iAcks), (head @(n - 1) iDats, iDats <<+ iDat))
  (y0, fb) <- feedbackC -< (fromShared, yn)
  idC -< y0

untilC
  :: (HiddenClockResetEnable dom, NFDataX a)
  => (a -> Bool)
  -> Circuit (Df dom a) (Df dom a)
  -> Circuit (Df dom a) (Df dom a)
untilC cond loop = circuit $ \a -> do
  b <- Df.registerBwd <| Df.select -< ([a, f], i)
  (c, d) <- Df.partition cond -< b
  let go x = if hasPayload x then pure 1 else pure 0
  (e, i) <- peek $ fmap go -< d
  f <- loop -< e
  idC -< c

--

toData :: (Bool, a) -> Df.Data a
toData (True, x) = pure x
toData _ = empty

fromData :: (NFDataX a) => Df.Data a -> (Bool, a)
fromData (Df.Data x) = (True, x)
fromData  Df.NoData  = (False, undefined)

hasPayload :: Df.Data a -> Bool
hasPayload Df.NoData = False
hasPayload _ = True

getPayloadUnsafe :: (NFDataX a) => Df.Data a -> a
getPayloadUnsafe = snd . fromData
