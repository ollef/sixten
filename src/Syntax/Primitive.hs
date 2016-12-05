{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Syntax.Primitive where

import Control.Monad
import Data.String

import qualified LLVM
import Syntax.Pretty

newtype Primitive v = Primitive { unPrimitive :: [PrimitivePart v] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable, Monoid)

data PrimitivePart v
  = TextPart LLVM.C
  | VarPart v
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

bindPrimitivePart :: (a -> Primitive b) -> PrimitivePart a -> Primitive b
bindPrimitivePart _ (TextPart t) = Primitive $ pure $ TextPart t
bindPrimitivePart f (VarPart v) = f v

instance Applicative Primitive where
  pure = return
  (<*>) = ap

instance Monad Primitive where
  return = Primitive . pure . pure
  Primitive xs >>= f = Primitive $ xs >>= unPrimitive . bindPrimitivePart f

instance IsString (Primitive v) where
  fromString = Primitive . pure . fromString

instance (IsString v, Pretty v)
      => Pretty (Primitive v) where
  prettyM (Primitive xs) = hsep $ prettyM <$> xs

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
