{-# LANGUAGE LambdaCase #-}

module Clash.GHC.PartialEval.Primitive.Strategy
  ( PrimImpl
  , liftId
  , liftNullary
  , liftUnary
  , liftBinary
  , liftBox
  , liftUndefined
  , fromValueForce
    -- Re-exported
  , Alternative(..)
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad.Catch (throwM)
import Data.Either (lefts)
import GHC.Stack (HasCallStack)

import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm
import Clash.Core.Term (Term, PrimInfo(..))

import Clash.GHC.PartialEval.Primitive.FromAst
import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.ToAst

type PrimImpl = (Term -> Eval Value) -> PrimInfo -> Args Value -> Eval Value

-- | The primitive is already a value, and is repackaged as a NePrim.
--
liftId :: PrimImpl
liftId _eval pr args =
  pure (VNeutral (NePrim pr args))

-- | The primitive takes no arguments, and has an implementation that is
-- available at run-time which can be lifted into Eval.
--
liftNullary :: (HasCallStack, ToAst a) => a -> PrimImpl
liftNullary result _eval pr args =
  case lefts args of
    [] -> do
      resTy <- resultType pr args
      toValue result resTy

    _ -> empty

-- | Lift a unary function to an implemenatation for a primitive operation.
-- This is used for primitives where the evaluation does not differ from the
-- semantics of the underlying Haskell implemenatation.
--
liftUnary :: (HasCallStack, FromAst a, ToAst b) => (a -> b) -> PrimImpl
liftUnary f eval pr args =
  case lefts args of
    [x] -> do
      result <- f <$> fromValueForce eval x
      resTy  <- resultType pr args
      toValue result resTy

    _ -> empty

-- | Lift a binary function to an implementation for a primitive operation.
-- See liftUnary for more information.
--
liftBinary
  :: (HasCallStack, FromAst a, FromAst b, ToAst c)
  => (a -> b -> c)
  -> PrimImpl
liftBinary f eval pr args =
  case lefts args of
    [x, y] -> do
      result <- f <$> fromValueForce eval x <*> fromValueForce eval y
      resTy  <- resultType pr args
      toValue result resTy

    _ -> empty

-- | Lift a constructor for a boxed type, e.g. I# for Int. Attempting to use
-- this function on other constructors may fail as it expects a unary
-- constructor.
--
liftBox :: (HasCallStack) => PrimImpl
liftBox _eval pr args =
  case args of
    [Left x] -> do
      [boxDc] <- resultDataCons (primType pr)
      VData boxDc [Left x] <$> getLocalEnv

    _ -> empty

liftUndefined :: (HasCallStack) => PrimImpl
liftUndefined _ _ _ = throwM ResultUndefined

-- | Attempt to use fromValue without evaluating the term. If it fails,
-- force evaluation of the term and attempt to use fromValue again.
--
-- If the value is undefined, this throws ResultUndefined.
--
fromValueForce
  :: (HasCallStack, FromAst a)
  => (Term -> Eval Value)
  -> Value
  -> Eval a
fromValueForce eval x = do
  forced <- forceEval x
  if isUndefined forced then throwM ResultUndefined else fromValue forced
 where
  forceEval = \case
    VThunk term env -> setLocalEnv env (eval term)
    value -> pure value
