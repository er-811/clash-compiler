{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.Vector
  ( vectorPrims
  ) where

import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import           Data.Text (Text)

import Data.Proxy
import Data.Reflection (reifyNat)
import GHC.TypeLits (KnownNat, type (*))

import Clash.Promoted.Nat (snatProxy)
import Clash.Sized.Internal.BitVector (BitVector)
import Clash.Sized.Vector as Vec (Vec, unconcatBitVector#, replicate)

import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm

import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Strategy
import Clash.GHC.PartialEval.Primitive.ToAst

vectorPrims :: HashMap Text PrimImpl
vectorPrims = HashMap.fromList
  [ ("Clash.Sized.Vector.splitAt", liftId) -- TODO
    -- TODO These two seem to be special.
  , ("Clash.Sized.Vector.index_int", liftId) -- TODO
  , ("Clash.Sized.Vector.replace_int", liftId) -- TODO
  , ("Clash.Sized.Vector.replicate", primReplicate)
  , ("Clash.Sized.Vector.splitAt", primSplitAt
  , ("Clash.Sized.Vector.concatBitVector#", liftId) -- TODO
  , ("Clash.Sized.Vector.unconcatBitVector#", primUnconcatBitVector)
  ]

primReplicate :: PrimImpl
primReplicate _eval pr args
  | [Right nTy, Right _aTy, Left _x, Left y] <- args
  = do szN <- typeSize nTy Nothing
       reifyNat szN (\pN -> go pN y)

  | otherwise
  = empty
 where
  go :: forall n. (KnownNat n) => Proxy n -> Value -> Eval Value
  go pN x = do
    resTy <- resultType pr args
    let sN = snatProxy pN

    toValue @(Vec n Value) (Vec.replicate sN x) resTy

primSplitAt :: PrimImpl
primSplitAt _eval pr args
  | [Right m, Right n, Right a, Left sM, Left x] <- args
  = _

  | otherwise
  = empty

primUnconcatBitVector :: PrimImpl
primUnconcatBitVector e p args
  | [Right n, Right m, Left knN, Left knM, Left x] <- args
  = do szN <- typeSize n (Just knN)
       szM <- typeSize m (Just knM)
       reifyNat szN (\pN -> reifyNat szM (\pM -> go pN pM x))

  | otherwise
  = empty
 where
  go :: forall n m. (KnownNat n, KnownNat m)
     => Proxy n -> Proxy m -> Value -> Eval Value
  go Proxy Proxy x = do
    a <- fromValueForce @(BitVector (n * m)) e x
    resTy <- resultType p args

    toValue @(Vec n (BitVector m)) (unconcatBitVector# @n @m a) resTy
