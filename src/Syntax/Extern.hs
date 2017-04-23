{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings #-}
module Syntax.Extern where

import Data.Monoid
import Data.Text(Text)

import Pretty

data Language = C
  deriving (Eq, Ord, Show)

data Extern a = Extern Language [ExternPart a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ExternPart a
  = ExternPart Text
  | ExprMacroPart a
  | TypeMacroPart a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty Language where
  prettyM C = "C"

instance Pretty a => Pretty (Extern a) where
  prettyM (Extern lang parts)
    = "(" <> prettyM lang <> "|" <> hcat (prettyM <$> parts) <> "|)"

instance Pretty a => Pretty (ExternPart a) where
  prettyM part = case part of
    ExternPart t -> prettyM t
    ExprMacroPart e -> prettyTightApp "$" (prettyM e) <> " "
    TypeMacroPart t -> prettyTightApp "$type:" (prettyM t) <> " "
