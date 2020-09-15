{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Promoted
  ( promotedPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)

-- import Clash.Promoted.Nat

import Clash.GHC.PartialEval.Primitive.Strategy

promotedPrims :: HashMap Text PrimImpl
promotedPrims = HashMap.fromList
  [ ("Clash.Promoted.Symbol.SSymbol", liftId)
  ]
