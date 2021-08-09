import           Data.Coerce (coerce)

import           Clash.Prelude
import           Clash.Explicit.Testbench (tbSystemClockGen, outputVerifier', stimuliGenerator)

import           Protocols (toSignals)
import qualified Protocols.Df as Df

import           ExeUnit (mkBram1, mkBram1reg, mkBram2, share, untilC)

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
    done         = expectOutput (bramReader clk rst en testInput)
    en           = enableGen
    clk          = tbSystemClockGen (not <$> done)
    rst          = systemResetGen

--

{-# ANN sharedBram
    (Synthesize
        { t_name   = "sharedBram"
        , t_inputs = [ PortName "clk"
                     , PortName "rst"
                     , PortName "en"
                     , PortName "rdaddr"
                     , PortProduct "" [PortName "wraddr", PortName "din"]
                     ]
        , t_output = PortProduct "" [PortName "dout1", PortName "dout2"]
        }) #-}
sharedBram
    :: Clock System
    -> Reset System
    -> Enable System
    -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
    -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
    -> Signal System (Bool, Bool, Df.Data BramData, Df.Data BramData)
sharedBram = exposeClockResetEnable $ \din0 din1 -> let
    bramC = circuit $ \(a, b) -> do
        [c, d] <- share . mkBram1 $ iterateI (1 +) 0 -< [a, b]
        idC -< (c, d)
    ((ack0, ack1), (dout0, dout1)) = toSignals bramC ((din0, din1), (pure def, pure def))
    in bundle (coerce <$> ack0, coerce <$> ack1, dout0, dout1)
{-# NOINLINE sharedBram #-}

sharedBramTb :: Signal System Bool
sharedBramTb = done where
    testInput1   = stimuliGenerator clk rst (            empty:>           empty:>pure (1, Just (1, 42)):>                 empty:>                  empty:>           empty:>                 empty:>Nil)
    testInput2   = stimuliGenerator clk rst (            empty:>      pure (1,x):>            pure (1,x):>            pure (1,x):>                  empty:>      pure (0,x):>                 empty:>Nil) where x = Nothing
    expectOutput = outputVerifier'  clk rst ((False,False,x,x):>(False,True,x,x):> (True,False,x,pure 1):>(False,True,pure 42,x):>(False,False,x,pure 42):>(False,True,x,x):>(False,False,x,pure 0):>Nil) where x = empty
    done         = expectOutput (sharedBram clk rst en testInput1 testInput2)
    en           = enableGen
    clk          = tbSystemClockGen (not <$> done)
    rst          = systemResetGen

--

{-# ANN sharedBram'
    (Synthesize
        { t_name   = "sharedBram'"
        , t_inputs = [ PortName "clk"
                     , PortName "rst"
                     , PortName "en"
                     , PortName "rdaddr"
                     , PortProduct "" [PortName "wraddr", PortName "din"]
                     ]
        , t_output = PortProduct "" [PortName "dout1", PortName "dout2"]
        }) #-}
sharedBram'
    :: Clock System
    -> Reset System
    -> Enable System
    -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
    -> Signal System (Df.Data (BramAddr, Maybe (BramAddr, BramData)))
    -> Signal System (Bool, Bool, Df.Data BramData, Df.Data BramData)
sharedBram' = exposeClockResetEnable $ \din0 din1 -> let
    bramC = circuit $ \(a, b) -> do
        [c, d] <- share . mkBram1reg $ iterateI (1 +) 0 -< [a, b]
        idC -< (c, d)
    ((ack0, ack1), (dout0, dout1)) = toSignals bramC ((din0, din1), (pure def, pure def))
    in bundle (coerce <$> ack0, coerce <$> ack1, dout0, dout1)
{-# NOINLINE sharedBram' #-}

sharedBramTb' :: Signal System Bool
sharedBramTb' = done where
    testInput1   = stimuliGenerator clk rst (            empty:>           empty:>pure (1, Just (1, 42)):>pure (1, Just (1, 42)):>            empty:>                 empty:>            empty:>                  empty:>Nil)
    testInput2   = stimuliGenerator clk rst (            empty:>      pure (1,x):>                 empty:>            pure (1,x):>       pure (1,x):>            pure (1,x):>            empty:>                  empty:>Nil) where x = Nothing
    expectOutput = outputVerifier'  clk rst ((False,False,x,x):>(False,True,x,x):>     (False,False,x,x):> (True,False,x,pure 1):>(False,False,x,x):>(False,True,pure 42,x):>(False,False,x,x):>(False,False,x,pure 42):>Nil) where x = empty
    done         = expectOutput (sharedBram' clk rst en testInput1 testInput2)
    en           = enableGen
    clk          = tbSystemClockGen (not <$> done)
    rst          = systemResetGen

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
    done         = expectOutput (tailRecursion clk rst en testInput)
    en           = enableGen
    clk          = tbSystemClockGen (not <$> done)
    rst          = systemResetGen

--

main :: IO ()
main = do
    print $ sampleN 9 bramReaderTb
    print $ sampleN 9 sharedBramTb
    print $ sampleN 10 sharedBramTb'
    print $ sampleN 10 tailRecursionTb
