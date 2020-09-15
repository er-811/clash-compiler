{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Natural
  ( naturalPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Natural
import GHC.Types

import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.Unboxed

naturalPrims :: HashMap Text PrimImpl
naturalPrims = HashMap.fromList
  [ ("GHC.Natural.naturalToInteger", liftUnary naturalToInteger)
  , ("GHC.Natural.naturalFromInteger", liftUnary naturalFromInteger)
  , ("GHC.Natural.plusNatural", liftBinary plusNatural)
  , ("GHC.Natural.timesNatural", liftBinary timesNatural)
  , ("GHC.Natural.minusNatural", liftBinary minusNatural)
  , ("GHC.Natural.wordToNatural#", primWordToNatural)
  , ("GHC.Natural.gcdNatural", liftBinary gcdNatural)
--, ("GHC.Natural.$wshiftLNatural", _)
  , ("GHC.Natural.NatS#", primNatS)
  ]

primWordToNatural :: PrimImpl
primWordToNatural =
  liftUnary $ \x ->
    let !(UWord (W# a)) = x in wordToNatural# a

primNatS :: PrimImpl
primNatS =
  liftUnary $ \x ->
    let !(UWord (W# a)) = x in NatS# a
