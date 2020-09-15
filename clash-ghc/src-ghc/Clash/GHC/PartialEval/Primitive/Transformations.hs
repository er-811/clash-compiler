{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Transformations
  ( transformationsPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Types (Int(..))

import Clash.GHC.PartialEval.Primitive.Strategy

transformationsPrims :: HashMap Text PrimImpl
transformationsPrims = HashMap.fromList
  [ ("EmptyCase", liftId)
  , ("Clash.Transformations.eqInt", primEqInt)
  , ("Clash.Transformations.removedArg", liftId)
  , ("Clash.Transformations.undefined", liftId)
  , ("Clash.Transformations.ref", liftId)

    -- Not transformations, but must be saved from defaulting to core.
    -- In the future preventing core unfolding should be default.

  , ("Clash.Explicit.BlockRam.blockRam#", liftId)
  , ("Clash.Explicit.BlockRam.blockRamU#", liftId)
  , ("Clash.Explicit.BlockRam.blockRam1#", liftId)
  , ("Clash.Explicit.BlockRam.File.blockRamFile#", liftId)

  , ("Clash.Explicit.DDR.ddrIn#", liftId)

  , ("Clash.Explicit.SimIO.apSimIO#", liftId)
  , ("Clash.Explicit.SimIO.bindSimIO#", liftId)
  , ("Clash.Explicit.SimIO.closeFile", liftId)
  , ("Clash.Explicit.SimIO.display", liftId)
  , ("Clash.Explicit.SimIO.finish", liftId)
  , ("Clash.Explicit.SimIO.flush", liftId)
  , ("Clash.Explicit.SimIO.fmapSimIO#", liftId)
  , ("Clash.Explicit.SimIO.getChar", liftId)
  , ("Clash.Explicit.SimIO.getLine", liftId)
  , ("Clash.Explicit.SimIO.isEOF", liftId)
  , ("Clash.Explicit.SimIO.mealyIO", liftId)
  , ("Clash.Explicit.SimIO.openFile", liftId)
  , ("Clash.Explicit.SimIO.pureSimIO#", liftId)
  , ("Clash.Explicit.SimIO.putChar", liftId)
  , ("Clash.Explicit.SimIO.readReg", liftId)
  , ("Clash.Explicit.SimIO.reg", liftId)
  , ("Clash.Explicit.SimIO.rewind", liftId)
  , ("Clash.Explicit.SimIO.seek", liftId)
  , ("Clash.Explicit.SimIO.tell", liftId)
  , ("Clash.Explicit.SimIO.unSimIO#", liftId)
  , ("Clash.Explicit.SimIO.writeReg", liftId)

  , ("Clash.Explicit.Testbench.assert", liftId)
  , ("Clash.Explicit.Testbench.assertBitVector", liftId)
  , ("Clash.Explicit.Testbench.tbClockGen", liftId)
  , ("Clash.Explicit.Testbench.tbEnableGen", liftId)

  , ("Clash.Explicit.Signal.veryUnsafeSynchronizer", liftId)

  , ("Clash.Prelude.ROM.asyncRom#", liftId)

  , ("Clash.Signal.Internal.clockGen", liftId)
  , ("Clash.Signal.Internal.delay#", liftId)
  , ("Clash.Signal.Internal.register#", liftId)
  , ("Clash.Signal.Internal.asyncRegister#", liftId)
  , ("Clash.Signal.Internal.syncRegister#", liftId)
  , ("Clash.Signal.Internal.unsafeFromReset", liftId)
  , ("Clash.Signal.Internal.unsafeToReset", liftId)
  , ("Clash.Signal.Internal.resetGenN", liftId)

  , ("Clash.NFDataX.deepErrorX", liftUndefined)
  , ("Clash.NFDataX.rnfx", liftId)
  , ("Clash.NFDataX.hasUndefined", liftId)
  , ("Clash.NFDataX.ensureSpine", liftId)

  , ("Clash.XException.errorX", liftUndefined)
  , ("Clash.XException.seqX", liftId)
  , ("Clash.XException.deepseqX", liftId)
  , ("Clash.XException.hwSeqX", liftId)

  , ("Clash.Intel.ClockGen.altpll", liftId)

  , ("Clash.Xilinx.ClockGen.clockWizard", liftId)
  , ("Clash.Xilinx.ClockGen.clockWizardDifferential", liftId)
  ]

primEqInt :: PrimImpl
primEqInt =
  liftBinary $ \x y ->
    let !(I# _) = x
        !(I# _) = y
     in x == y
