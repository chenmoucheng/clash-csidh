module TopEntity where

import Clash.Prelude
import Protocols (toSignals)

import ExeUnit   (mkBram2, toData, fromData)

type BramAddr = Unsigned 10
type BramData = Unsigned 32

{-# ANN myipclash
  (Synthesize
    { t_name   = "myipclash"
    , t_inputs = [ PortName "clk"
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
  rdsig = bundle (rden, addr)
  wrsig = bundle (wren, bundle (addr, din))
  bram = toSignals . mkBram2 $ repeat 0
  (_, dout) = bram ((toData <$> rdsig, toData <$> wrsig), pure def)
  in snd . fromData <$> dout
