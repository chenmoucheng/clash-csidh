{-# LANGUAGE DeriveAnyClass #-}

module ExeUnit
  ( dsp48mult
  , mkExeUnit
  , mkBram1
  , mkBram2
  , toData
  , fromData
  , hasPayload
  , getPayloadUnsafe
  ) where

import           Data.Bifunctor               (first)
import           Data.Coerce                  (coerce)
import           Data.Proxy                   (Proxy(..))
import           Data.String.Interpolate      (i)
import           Data.String.Interpolate.Util (unindent)

import           Clash.Annotations.Primitive (HDL(..), Primitive(..))
import           Clash.Prelude
import           Protocols (Circuit(..), Df, Protocol(..), (|>), toSignals)
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
