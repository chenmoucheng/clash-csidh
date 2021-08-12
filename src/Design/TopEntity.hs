{-# OPTIONS_GHC -fplugin Protocols.Plugin #-}

module Design.TopEntity where

import qualified NumericPrelude as NP
import qualified MathObj.Wrapper.Haskell98 as W

import Clash.Prelude
import Protocols (Circuit(..), Df, (<|), toSignals)
import qualified Protocols.Df as Df

import ExeUnit (fromData, mkBram2, bram1Reader, bram1Writer, shareEx, shareEx', toData)
import qualified PrimeField.MontgomeryN

type BramAddr = Unsigned 10
type BramData = Unsigned 32

{-# ANN myipclash
  (Synthesize
    { t_name   = "myipclash"
    , t_inputs =
      [ PortName "clk"
      , PortName "rst"
      , PortName "en"
      , PortName "rden"
      , PortName "addr"
      , PortName "wren"
      , PortName "data_in"
      ]
    , t_output = PortName "data_out"
    }) #-}
myipclash
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System Bool
  -> Signal System BramAddr
  -> Signal System Bool
  -> Signal System BramData
  -> Signal System BramData
myipclash = exposeClockResetEnable $ \rden addr wren din -> let
  rdDf = toData <$> bundle (rden, addr)
  wrDf = toData <$> bundle (wren, bundle (addr, din))
  ctDf = toData <$> bundle (wren .&&. (0 ==) <$> addr, din)
  (_, dout) = toSignals master ((rdDf, wrDf, ctDf), pure def)
  in snd . fromData <$> dout

master
  :: (HiddenClockResetEnable dom)
  => Circuit (Df dom BramAddr, Df dom (BramAddr, BramData), Df dom BramData) (Df dom BramData)
master = circuit $ \(rdDf, wrDf, ctDf) -> do
  bramOut <- mkBram2 $ repeat 0 -< (bramRdIn, bramWrIn)
  (bramRdIn, [dout, sharedOut]) <- shareEx -< ([rdDf, sharedRdIn], bramOut)
  bramWrIn <- shareEx' -< [wrDf, sharedWrIn]
  (sharedRdIn, sharedWrIn) <- slave -< (ctDf, sharedOut)
  idC -< dout

slave
  :: (HiddenClockResetEnable dom)
  => Circuit (Df dom BramData, Df dom BramData) (Df dom BramAddr, Df dom (BramAddr, BramData))
slave = circuit $ \(ctDf, sharedOut) -> do
  baseAddr <- Df.map (unpack . resize . pack) -< ctDf
  [rdAddr, wrAddr] <- Df.fanout -< baseAddr
  (sharedRdIn, x) <- bram1Reader @(PrimeField.MontgomeryN.T 256 64 (W.T (Unsigned 18))) -< (rdAddr, sharedOut)
  let double x = x NP.+ x
  y <- Df.map double -< x
  sharedWrIn <- bram1Writer <| Df.zip -< (wrAddr, y)
  idC -< (sharedRdIn, sharedWrIn)

deriving instance (NFDataX a) => (NFDataX (W.T a))
