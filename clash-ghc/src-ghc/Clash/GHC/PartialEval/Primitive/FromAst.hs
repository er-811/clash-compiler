{-|
-}

{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Primitive.FromAst
  ( FromAst(..)
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad (guard)
import Data.Primitive.ByteArray (ByteArray(..))
import Data.Proxy
import Data.Reflection (reifyNat)
import GHC.Integer.GMP.Internals (Integer(..), BigNat(..))
import GHC.Natural (Natural(..))
import GHC.Stack (HasCallStack)
import GHC.TypeLits (KnownNat)
import GHC.Types (Int(..), Word(..))
import Unsafe.Coerce

import PrelNames
import Unique (getKey)

import Clash.Sized.Internal.BitVector as BV
import Clash.Sized.Internal.Index as I
import Clash.Sized.Internal.Signed as S
import Clash.Sized.Internal.Unsigned as U
import Clash.Sized.Vector as Vec

import Clash.Core.DataCon
import Clash.Core.Literal
import Clash.Core.PartialEval.Monad
import Clash.Core.PartialEval.NormalForm
import Clash.Core.Term (PrimInfo(..))

import Clash.GHC.PartialEval.Primitive.Info
import Clash.GHC.PartialEval.Primitive.Unboxed

-- import Clash.Debug -- TODO

-- | FromAst gets value of a given type from some representation of an AST.
-- Failure means that the AST does not represent the value directly, but some
-- computation that returns a value of the desired type.
--
-- Extracting from Term or Value means primitives can be implemented lazily.
-- Consider the Term AST for
--
--   True && (let ... in False)
--
-- Initially, fromTerm can be used to potentially extract a value without
-- evaluating the term. This works for the LHS of (&&), but not the RHS.
-- However, if the RHS is evaluated, then fromValue will yield the False,
-- allowing the primitive (&&) to be evaluated. With judicial use of evaluate,
-- primitives can be implemented as lazy in all arguments desired.
--
class FromAst a where
  fromValue :: (HasCallStack) => Value -> Eval a

instance FromAst Value where
  fromValue = pure

instance FromAst BigNat where
  fromValue (stripValue -> value) =
    case value of
      VData _dc [Left x] env ->
        setLocalEnv env $ do
          !(ByteArray ba) <- boxByteArray <$> fromValue x
          pure (BN# ba)

      _ -> empty

instance FromAst Bool where
  fromValue (stripValue -> value) =
    case value of
      VData dc [] _env
        | dcUniq dc == getKey falseDataConKey -> pure False
        | dcUniq dc == getKey trueDataConKey  -> pure True

      _ -> empty

instance FromAst UByteArray where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (ByteArrayLiteral ba) -> pure (UByteArray ba)
      _ -> empty

instance FromAst Char where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left x]) -> do
        guard (primName pr == "GHC.Types.C#")
        boxChar <$> fromValue x

      VData dc [Left x] env ->
        setLocalEnv env $ do
          guard (dcUniq dc == getKey charDataConKey)
          boxChar <$> fromValue x

      _ -> empty

instance FromAst UChar where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (CharLiteral c) -> pure (UChar c)
      _ -> empty

instance FromAst Integer where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (IntegerLiteral x) -> pure x

      VData dc [Left x] env ->
        setLocalEnv env $
          case dcTag dc of
            1 -> do
              !(UInt (I# i)) <- fromValue x
              pure (S# i)

            2 -> do
              !(UByteArray (ByteArray ba)) <- fromValue x
              pure (Jp# (BN# ba))

            3 -> do
              !(UByteArray (ByteArray ba)) <- fromValue x
              pure (Jn# (BN# ba))

            _ -> empty

      _ -> empty

instance FromAst Int where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left x]) -> do
        guard (primName pr == "GHC.Types.I#")
        boxInt <$> fromValue x

      VData dc [Left x] env ->
        setLocalEnv env $ do
          guard (dcUniq dc == getKey intDataConKey)
          boxInt <$> fromValue x

      _ -> empty

instance FromAst UInt where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (IntLiteral x) -> pure (UInt (fromInteger x))
      _ -> empty

instance FromAst Natural where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (NaturalLiteral x) ->
        pure (fromInteger x)

      VData dc [Left x] env ->
        setLocalEnv env $
          case dcTag dc of
            1 -> do
              !(UWord (W# i)) <- fromValue x
              pure (NatS# i)

            2 -> do
              !(UByteArray (ByteArray ba)) <- fromValue x
              pure (NatJ# (BN# ba))

            _ -> empty

      _ -> empty

instance FromAst Word where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left x]) -> do
        guard (primName pr == "GHC.Types.W#")
        boxWord <$> fromValue x

      VData dc [Left x] env ->
        setLocalEnv env $ do
          guard (dcUniq dc == getKey wordDataConKey)
          boxWord <$> fromValue x

      _ -> empty

instance FromAst UWord where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (WordLiteral x) -> pure (UWord (fromInteger x))
      _ -> empty

instance FromAst Float where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left x]) -> do
        guard (primName pr == "GHC.Types.F#")
        boxFloat <$> fromValue x

      VData dc [Left x] env ->
        setLocalEnv env $ do
          guard (dcUniq dc == getKey floatDataConKey)
          boxFloat <$> fromValue x

      _ -> empty

instance FromAst UFloat where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (FloatLiteral x) -> pure (UFloat (fromRational x))
      _ -> empty

instance FromAst Double where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left x]) -> do
        guard (primName pr == "GHC.Types.D#")
        boxDouble <$> fromValue x

      VData dc [Left x] env ->
        setLocalEnv env $ do
          guard (dcUniq dc == getKey doubleDataConKey)
          boxDouble <$> fromValue x

      _ -> empty

instance FromAst UDouble where
  fromValue (stripValue -> value) =
    case value of
      VLiteral (DoubleLiteral x) -> pure (UDouble (fromRational x))
      _ -> empty

instance FromAst Bit where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Left m, Left i]) -> do
        guard (primName pr == "Clash.Sized.Internal.BitVector.fromInteger##")
        !(UWord (W# mask)) <- fromValue m
        !int <- fromValue i

        pure (BV.fromInteger## mask int)

      _ -> empty

instance FromAst (BitVector n) where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Right n, Left knN, Left m, Left i]) -> do
        guard (primName pr == "Clash.Sized.Internal.BitVector.fromInteger#")
        szN <- typeSize n (Just knN)

        reifyNat szN (\pN -> unsafeCoerce (go pN m i))

      _ -> empty
   where
    go :: forall m. (KnownNat m)
       => Proxy m -> Value -> Value -> Eval (BitVector m)
    go Proxy m i = do
      m' <- fromValue m
      i' <- fromValue i
      pure (BV.fromInteger# m' i')

instance FromAst (Index n) where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Right n, Left knN, Left i]) -> do
        guard (primName pr == "Clash.Sized.Internal.Index.fromInteger#")
        szN <- typeSize n (Just knN)
        reifyNat szN (\pN -> unsafeCoerce (go pN i))

      _ -> empty
   where
    go :: forall m. (KnownNat m) => Proxy m -> Value -> Eval (Index m)
    go Proxy i = I.fromInteger# <$> fromValue i

instance FromAst (Signed n) where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Right n, Left knN, Left i]) -> do
        guard (primName pr == "Clash.Sized.Internal.Signed.fromInteger#")
        szN <- typeSize n (Just knN)
        reifyNat szN (\pN -> unsafeCoerce (go pN i))

      _ -> empty
   where
    go :: forall m. (KnownNat m) => Proxy m -> Value -> Eval (Signed m)
    go Proxy i = S.fromInteger# <$> fromValue i

instance FromAst (Unsigned n) where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Right n, Left knN, Left i]) -> do
        guard (primName pr == "Clash.Sized.Internal.Unsigned.fromInteger#")
        szN <- typeSize n (Just knN)
        reifyNat szN (\pN -> unsafeCoerce (go pN i))

      _ -> empty
   where
    go :: forall m. (KnownNat m) => Proxy m -> Value -> Eval (Unsigned m)
    go Proxy i = U.fromInteger# <$> fromValue i

{-
instance (FromAst a) => FromAst (LVec a) where
  fromTerm (stripTicks -> term)
    | Data _dc `TyApp` _nTy `TyApp` _aTy `App` _co <- term
    = pure LNil

    | Data _dc `TyApp` _nTy `TyApp` _aTy `TyApp` _eTy `App` _co `App` x `App` y <- term
    = do a <- fromTerm x
         pure (LCons a y)

    | otherwise
    = empty
-}

instance (FromAst a) => FromAst (Ref a) where
  fromValue (stripValue -> value) =
    case value of
      VNeutral (NePrim pr [Right _a, Left i]) -> do
        guard (primName pr == "Clash.Transformations.ref")
        !(UInt addr) <- fromValue i
        refVal <- getRef addr >>= fromValue

        pure (Ref (Just addr) refVal)

      _ -> empty
