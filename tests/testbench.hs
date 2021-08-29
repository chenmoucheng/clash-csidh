import           Data.Coerce (coerce)

import           Clash.Prelude
import           Clash.Explicit.Testbench (tbSystemClockGen, outputVerifier', stimuliGenerator)

import           Protocols ((<|), (|>), toSignals)
import qualified Protocols.Df as Df

import           ExeUnit (bram1Reader, bram1Writer, foldlC, foldrC, mkBram1, mkBram2, share, shareEx, shareEx', untilC)

--

type BramAddr = Unsigned 4
type BramData = Unsigned 32

{-# ANN bramReader
  (Synthesize
    { t_name   = "bramReader"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortProduct "" [PortName "addr", PortName "rden"]
           ]
    , t_output = PortProduct "" [PortName "ack", PortName "dout"]
    }) #-}
bramReader
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data BramAddr, Bool)
  -> Signal System (Bool, Df.Data BramData)
bramReader = exposeClockResetEnable $ bundle . (\(addr, ack) -> let
  bramC = mkBram2 $ iterateI (1 +) 0
  ((ack', _), dout) = toSignals bramC ((addr, pure empty), coerce <$> ack)
  in (coerce <$> ack', dout)) . unbundle
{-# NOINLINE bramReader #-}

bramReaderTb :: Signal System Bool
bramReaderTb = done where
  testInput    = stimuliGenerator clk rst ((pure 0,False):>(pure 1,  True):>(empty, False):>(empty,  True):>(empty,False):>(pure 2,False):>(pure 3,  True):>Nil)
  expectOutput = outputVerifier'  clk rst ((True  ,empty):>(True  ,pure 0):>(False,pure 1):>(False,pure 1):>(False,empty):>(True  ,empty):>(True  ,pure 2):>Nil)
  done     = expectOutput (bramReader clk rst en testInput)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

{-# ANN sharedBram1
  (Synthesize
    { t_name   = "sharedBram1"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortName "rdaddr"
           , PortProduct "" [PortName "wraddr", PortName "din"]
           ]
    , t_output = PortProduct "" [PortName "dout1", PortName "dout2"]
    }) #-}
sharedBram1
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
  -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
  -> Signal System (Bool, Bool, Df.Data BramData, Df.Data BramData)
sharedBram1 = exposeClockResetEnable $ \din0 din1 -> let
  bramC = circuit $ \(a, b) -> do
    [c, d] <- share . mkBram1 $ iterateI (1 +) 0 -< [a, b]
    idC -< (c, d)
  ((ack0, ack1), (dout0, dout1)) = toSignals bramC ((din0, din1), (pure def, pure def))
  in bundle (coerce <$> ack0, coerce <$> ack1, dout0, dout1)
{-# NOINLINE sharedBram1 #-}

sharedBram1Tb :: Signal System Bool
sharedBram1Tb = done where
  testInput1   = stimuliGenerator clk rst (            empty:>           empty:>pure (1, Just (1, 42)):>                 empty:>                  empty:>           empty:>                 empty:>Nil)
  testInput2   = stimuliGenerator clk rst (            empty:>      pure (1,x):>            pure (1,x):>            pure (1,x):>                  empty:>      pure (0,x):>                 empty:>Nil) where x = Nothing
  expectOutput = outputVerifier'  clk rst ((False,False,x,x):>(False,True,x,x):> (True,False,x,pure 1):>(False,True,pure 42,x):>(False,False,x,pure 42):>(False,True,x,x):>(False,False,x,pure 0):>Nil) where x = empty
  done     = expectOutput (sharedBram1 clk rst en testInput1 testInput2)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

{-# ANN sharedBram2
  (Synthesize
    { t_name   = "sharedBram2"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortName "rdaddr"
           , PortProduct "" [PortName "wraddr", PortName "din"]
           ]
    , t_output = PortProduct "" [PortName "dout1", PortName "dout2"]
    }) #-}
sharedBram2
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data BramAddr)
  -> Signal System (Df.Data (BramAddr, BramData))
  -> Signal System (Bool, Bool, Df.Data BramData)
sharedBram2 = exposeClockResetEnable $ \rdsigs wrsigs -> let
  bramC = circuit $ \(rdDf, wrDf) -> do
    bramOut <- mkBram2 $ iterateI (1 +) 0 -< (bramRdIn, bramWrIn)
    (bramRdIn, [dout]) <- shareEx Df.registerFwd -< ([rdDf], bramOut)
    bramWrIn <- shareEx' -< [wrDf]
    idC -< dout
  ((ack0, ack1), dout) = toSignals bramC ((rdsigs, wrsigs), pure def)
  in bundle (coerce <$> ack0, coerce <$> ack1, dout)
{-# NOINLINE sharedBram2 #-}

sharedBram2Tb :: Signal System Bool
sharedBram2Tb = done where
  testInput1   = stimuliGenerator clk rst (         empty :>        empty :>       pure 1 :>               empty :>   pure  2   :>              empty :>Nil)
  testInput2   = stimuliGenerator clk rst (         empty :>   pure (1,42):>        empty :>               empty :>   pure (2,0):>              empty :>Nil)
  expectOutput = outputVerifier'  clk rst ((False,False,x):>(False,True,x):>(True,False,x):>(False,False,pure 42):>(True,True,x):>(False,False,pure 0):>Nil) where x = empty
  done     = expectOutput (sharedBram2 clk rst en testInput1 testInput2)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

{-# ANN tailRecursion
  (Synthesize
    { t_name   = "tailRecursion"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortName "din"
           ]
    , t_output = PortProduct "" [PortName "ack", PortName "dout"]
    }) #-}
tailRecursion
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data BramAddr)
  -> Signal System (Bool, Df.Data BramAddr)
tailRecursion = exposeClockResetEnable $ \din -> let
  suc = circuit $ \x -> do
    z <- mkBram2 $ iterateI (1 +) 1 -< (x, y)
    y <- Df.pure empty
    idC -< z
  (ack, dout) = toSignals (untilC (> 2) suc) (din, pure def)
  in bundle (coerce <$> ack, dout)
{-# NOINLINE tailRecursion #-}

tailRecursionTb :: Signal System Bool
tailRecursionTb = done where
  testInput    = stimuliGenerator clk rst (         x:>   pure 1:>    pure 5:>    pure 5:>    pure 5:>    pure 5:>        pure 5:>              x:>Nil) where x = empty
  expectOutput = outputVerifier'  clk rst ((False, x):>(True, x):>(False, x):>(False, x):>(False, x):>(False, x):>(True, pure 3):>(False, pure 5):>Nil) where x = empty
  done     = expectOutput (tailRecursion clk rst en testInput)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

{-# ANN foldlCir
  (Synthesize
    { t_name   = "foldlCir"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortName "din"
           ]
    , t_output = PortProduct "" [PortName "ack", PortName "dout"]
    }) #-}
foldlCir
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data BramData)
  -> Signal System (Bool, Df.Data BramData)
foldlCir = exposeClockResetEnable $ \din -> let
  adderC = circuit $ \x -> do
    rdOut <- mkBram2 $ iterateI (1 +) 1 -< (rdIn, wrIn)
    wrIn <- Df.pure empty
    base <- Df.pure $ pure 0
    (rdIn, xs) <- bram1Reader @System @BramData @4 @(Vec 2 BramData) Df.registerFwd -< (base, rdOut)
    xs' <- Df.unbundleVec -< xs
    let cir = Df.map (uncurry (+)) |> Df.registerBwd
    y <- foldlC cir -< (xs', x)
    idC -< y
  (ack, dout) = toSignals adderC (din, pure def)
  in bundle (coerce <$> ack, dout)
{-# NOINLINE foldlCir #-}

foldlCirTb :: Signal System Bool
foldlCirTb = done where
  testInput    = stimuliGenerator clk rst ( pure 0       :> pure 0       :> pure 0       :> pure 0      :> empty        :> empty         :> pure 1      :> pure 2       :> pure 2        :>Nil)
  expectOutput = outputVerifier'  clk rst ((False, empty):>(False, empty):>(False, empty):>(True, empty):>(False, empty):>(False, pure 3):>(True, empty):>(False, empty):>(False, pure 4):>Nil)
  done     = expectOutput (foldlCir clk rst en testInput)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

{-# ANN foldrCir
  (Synthesize
    { t_name   = "foldrCir"
    , t_inputs = [ PortName "clk"
           , PortName "rst"
           , PortName "en"
           , PortName "din"
           ]
    , t_output = PortProduct "" [PortName "ack", PortName "dout"]
    }) #-}
foldrCir
  :: Clock System
  -> Reset System
  -> Enable System
  -> Signal System (Df.Data BramAddr, Df.Data BramAddr)
  -> Signal System (Bool, Bool, Df.Data BramData)
foldrCir = exposeClockResetEnable $ \din -> let
  multC = circuit $ \(rdBase, userIn) -> do
    rdOut <- mkBram2 $ iterateI (1 +) 1 -< (rdIn, wrIn)
    (rdIn, [readerOut, userOut]) <- shareEx Df.registerFwd -< ([readerIn, userIn], rdOut)
    (readerIn, xs) <- bram1Reader @System @BramData @4 @(Vec 3 BramData) Df.registerFwd -< (rdBase, readerOut)
    xs' <- Df.unbundleVec -< xs
    let cir = Df.map (uncurry (*)) |> Df.registerBwd
    wrBase <- Df.pure $ pure 5
    p <- Df.pure $ pure 1
    y <- foldrC cir -< (xs', p)
    wrIn <- bram1Writer @System @4 @BramData @BramData <| Df.zip -< (wrBase, y)
    idC -< userOut
  ((ack0, ack1), dout) = toSignals multC (unbundle din, pure def)
  in bundle (coerce <$> ack0, coerce <$> ack1, dout)
{-# NOINLINE foldrCir #-}

foldrCirTb :: Signal System Bool
foldrCirTb = done where
  testInput    = stimuliGenerator clk rst ((pure 1, pure 5)   :>(pure 1, pure 5)   :>(pure 1, pure 5)  :>(empty, pure 5)   :>(empty, pure 5)    :>(empty, pure 5)    :>(empty, pure 5)    :>(empty, pure 5)    :>(empty, pure 5)     :>Nil)
  expectOutput = outputVerifier'  clk rst ((False,False,empty):>(False,False,empty):>(True,False,empty):>(False,True,empty):>(False,True,pure 6):>(False,True,pure 6):>(False,True,pure 6):>(False,True,pure 6):>(False,True,pure 24):>Nil)
  done     = expectOutput (foldrCir clk rst en testInput)
  en       = enableGen
  clk      = tbSystemClockGen (not <$> done)
  rst      = systemResetGen

--

main :: IO ()
main = do
  print $ sampleN 9 bramReaderTb
  print $ sampleN 9 sharedBram1Tb
  print $ sampleN 8 sharedBram2Tb
  print $ sampleN 10 tailRecursionTb
  print $ sampleN 11 foldlCirTb
  print $ sampleN 11 foldrCirTb
