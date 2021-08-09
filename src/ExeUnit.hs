{-# LANGUAGE DeriveAnyClass #-}

module ExeUnit
  ( mkExeUnit
  , mkBram1reg
  , mkBram1
  , mkBram2
  , share
  , untilC
  , toData
  , fromData
  ) where

import           Data.Bifunctor (first)
import           Data.Coerce    (coerce)
import           Data.Proxy     (Proxy(..))

import           NumericPrelude (ifThenElse)

import           Clash.Prelude
import           Protocols (Circuit(..), Df, Protocol(..), (<|), (|>))
import qualified Protocols.Df as Df

-- $

data State (n :: Nat) = Idle | Busy (Index n) | Wait deriving (Eq, Show)
deriving instance (KnownNat n, 1 <= n) => Generic (State n)
deriving instance (KnownNat n, 1 <= n) => NFDataX (State n)
deriving instance (KnownNat n, 1 <= n) => ShowX (State n)

entryState :: forall n. (KnownNat n, 1 <= n) => State n
entryState = Busy . fromInteger $ natVal @(n - 1) Proxy

mkFSM
  :: forall n dom a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
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

isWait :: (State n, b) -> Bool
isWait (s, _) = s == Wait

isDone :: (KnownNat n, 1 <= n) => (State n, b) -> Bool
isDone (s, _) = s == Busy 0

poseAck :: (KnownNat n, 1 <= n) => (a, State n) -> Bool
poseAck (_, s) = s == entryState

canEn :: (a, State n) -> Bool
canEn (snd -> Busy _) = True
canEn _ = False

--

mkExeUnit
  :: forall n dom a b. (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => (Enable dom -> Signal dom a -> Signal dom b)
  -> Circuit (Df dom a) (Df dom b)
mkExeUnit f = Circuit . hideEnable $ \en (iDat, iAck) -> let
  s = mkFSM @n (iDat, iAck)
  oAck = coerce . poseAck <$> s
  en' = toEnable $ fromEnable en .&&. canEn <$> s
  fout = f en' (getPayloadUnsafe <$> iDat)
  oDat = toData <$> bundle (isDone <$> s .||. isWait <$> s, fout)
  in (oAck, oDat)

--

mkBram1reg
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => Vec (2 ^ n) a
  -> Circuit (Df dom (Unsigned n, Maybe (Unsigned n, a))) (Df dom a)
mkBram1reg contents = mkExeUnit @2 f where
  -- to avoid monomorphism restriction
  f x = (exposeEnable $ register undefined . uncurry (readNew $ blockRamPow2 contents) . unbundle) x

mkBram1
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => Vec (2 ^ n) a
  -> Circuit (Df dom (Unsigned n, Maybe (Unsigned n, a))) (Df dom a)
mkBram1 contents = mkExeUnit @1 f where
  -- to avoid monomorphism restriction
  f x = (exposeEnable $ uncurry (readNew $ blockRamPow2 contents) . unbundle) x

mkBram2
  :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n, NFDataX a)
  => Vec (2 ^ n) a
  -> Circuit (Df dom (Unsigned n), Df dom (Unsigned n, a)) (Df dom a)
mkBram2 contents = adpt |> bram where
  adpt = Circuit $ first unbundle . unbundle . fmap go . bundle . first bundle where
    go :: (NFDataX a) => ((Df.Data a, Df.Data b), Df.Ack (a, Maybe b)) -> ((Df.Ack a, Df.Ack b), Df.Data (a, Maybe b))
    go ((Df.Data x, Df.Data y), ack) = ((coerce ack, coerce ack), pure (x, Just y))
    go ((Df.Data x, Df.NoData), ack) = ((coerce ack, coerce False), pure (x, Nothing))
    go ((Df.NoData, Df.Data y), ack) = ((coerce False, coerce ack), pure (undefined, Just y))
    go _ = ((coerce False, coerce False), empty)
  bram = mkBram1 contents

--

peek :: (HiddenClockResetEnable dom, NFDataX b)
  => (Fwd a -> Fwd (Df dom b))
  -> Circuit a (a, Df dom b)
peek f = Circuit $ \(iDat, (iAck, ack)) -> let
  dat = f iDat
  sel = moore go id True $ bundle (hasPayload <$> dat, coerce <$> ack) where
    go True  (True, False) = False
    go False (_,     True) = True
    go s _ = s
  in (iAck, (iDat, mux sel dat $ register empty dat))

share :: (HiddenClockResetEnable dom, KnownNat n, 1 <= n)
  => Circuit (Df dom a) (Df dom b)
  -> Circuit (Vec n (Df dom a)) (Vec n (Df dom b))
share cir = circuit $ \xs -> do
  let selC = peek $ fmap (maybe empty pure . findIndex hasPayload) . bundle
  (ys, i) <- selC -< xs
  [j, k] <- Df.fanout -< i
  x <- cir <| Df.select -< (ys, j)
  l <- Df.registerFwd -< k
  zs <- Df.route <| Df.zip -< (l, x)
  idC -< zs

untilC :: (HiddenClockResetEnable dom, NFDataX a)
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
