{-|
Copyright   : (C) 2020, QBayLogic B.V.
License     : BSD2 (see the file LICENSE)
Maintainer  : QBayLogic B.V. <devops@qbaylogic.com>

Newtypes for unboxed versions of types used in the partial evaluator. These
are needed, as it is not possible to write instances of FromAst / ToAst using
the actual unboxed types.
-}

module Clash.GHC.PartialEval.Primitive.Unboxed where

import Data.Primitive.ByteArray (ByteArray)

newtype UByteArray
  = UByteArray { boxByteArray :: ByteArray }

newtype UChar
  = UChar { boxChar :: Char }

newtype UInt
  = UInt { boxInt :: Int }

newtype UWord
  = UWord {boxWord :: Word }

newtype UFloat
  = UFloat { boxFloat :: Float }

newtype UDouble
  = UDouble { boxDouble :: Double }

newtype UTuple2 a b
  = UTuple2 { boxTuple2 :: (a, b) }

newtype UTuple4 a b c d
  = UTuple4 { boxTuple4 :: (a, b, c, d) }

-- TODO Maybe these should be in strategy?

data Ref a = Ref
  { refAddr :: Maybe Int
  , refValue :: a
  }

{-
data LVec a
  = LNil
  | LCons a Term
-}
