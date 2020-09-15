{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Enum
  ( enumPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import qualified Data.List as List (find)
import Data.Text (Text)

import Clash.Core.DataCon
import Clash.Core.Term
import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm

import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.Unboxed

enumPrims :: HashMap Text PrimImpl
enumPrims = HashMap.fromList
  [ ("GHC.Prim.tagToEnum#", primTagToEnum)
  ]

primTagToEnum :: PrimImpl
primTagToEnum e _ args
  | [Right ty, Left x] <- args
  = do env <- getLocalEnv
       dcs <- resultDataCons ty
       UInt a <- fromValueForce e x

       case List.find (\dc -> dcTag dc == a + 1) dcs of
         Just dc -> pure (VThunk (Data dc) env)
         _ -> empty

  | otherwise
  = empty
