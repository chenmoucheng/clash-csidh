{-# OPTIONS_GHC -fplugin Protocols.Plugin #-}

module Design.TopEntity where

import qualified MathObj.Wrapper.Haskell98 as W

import Clash.Prelude
import Protocols (Circuit(..), Df, (<|), toSignals)
import qualified Protocols.Df as Df

import Edsl    (bram1Reader, bram1Writer, shareEx, shareEx')
import ExeUnit (dsp48mult, fromData, mkBram2, toData)

--

type BramAddr = Unsigned 8
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

--

master
  :: (HiddenClockResetEnable dom)
  => Circuit (Df dom BramAddr, Df dom (BramAddr, BramData), Df dom BramData) (Df dom BramData)
master = circuit $ \(rdDf, wrDf, ctDf) -> do
  bramOut <- mkBram2 $ repeat 0 -< (bramRdIn, bramWrIn)
  (bramRdIn, [dout, toSlaveData]) <- shareEx Df.registerFwd -< ([rdDf, fromSlaveRd], bramOut)
  bramWrIn <- shareEx' -< [wrDf, fromSlaveWr]
  toSlaveCntl <- Df.registerFwd -< ctDf
  (fromSlaveRd, fromSlaveWr) <- slave -< (toSlaveCntl, toSlaveData)
  idC -< dout

slave
  :: (HiddenClockResetEnable dom)
  => Circuit (Df dom BramData, Df dom BramData) (Df dom BramAddr, Df dom (BramAddr, BramData))
slave = circuit $ \(fromMaster, fromBram) -> do
  baseAddr <- Df.map (unpack . resize . pack) -< fromMaster
  [rdAddr, wrAddr] <- Df.fanout -< baseAddr
  (toBramRd, x) <- bram1Reader @_ @_ @_ @(Unsigned 64) Df.registerFwd -< (rdAddr, fromBram)
  [x1, x2] <- Df.fanout -< x
  y <- Df.registerBwd <| Df.map (uncurry (dsp48mult @36)) <| Df.zip -< (x1, x2)
  toBramWr <- bram1Writer <| Df.zip -< (wrAddr, y)
  idC -< (toBramRd, toBramWr)

deriving instance (NFDataX a) => (NFDataX (W.T a))
