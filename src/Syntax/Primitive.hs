{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Syntax.Primitive where

import Control.Monad
import Data.String

import qualified Backend.LLVM as LLVM
import Pretty
import Syntax.Direction

data Primitive v = Primitive
  { primitiveDir :: Direction
  , unPrimitive :: [PrimitivePart v]
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data PrimitivePart v
  = TextPart LLVM.C
  | VarPart v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (IsString v, Pretty v)
      => Pretty (Primitive v) where
  prettyM (Primitive d xs) = prettyM d <+> hsep (prettyM <$> xs)

instance Applicative PrimitivePart where
  pure = VarPart
  (<*>) = ap

instance Monad PrimitivePart where
  return = VarPart
  TextPart t >>= _ = TextPart t
  VarPart v >>= f = f v

instance IsString (PrimitivePart v) where
  fromString = TextPart . fromString

instance (IsString v, Pretty v)
      => Pretty (PrimitivePart v) where
  prettyM pp = case pp of
    TextPart t -> prettyM t
    VarPart v -> prettyM v
