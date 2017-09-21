{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings, TemplateHaskell #-}
module Syntax.Extern where

import Data.Monoid
import Data.Text(Text)
import Data.Deriving

import Pretty

data Language = C
  deriving (Eq, Ord, Show)

data Extern a = Extern Language [ExternPart a]
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data TargetMacro
  = PointerAlignment
  deriving (Eq, Ord, Show)

data ExternPart a
  = ExternPart Text
  | ExprMacroPart a
  | TypeMacroPart a
  | TargetMacroPart TargetMacro
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

deriveEq1 ''ExternPart
deriveOrd1 ''ExternPart
deriveShow1 ''ExternPart
deriveEq1 ''Extern
deriveOrd1 ''Extern
deriveShow1 ''Extern

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
    TargetMacroPart t -> prettyTightApp "$target:" (prettyM t) <> " "

instance Pretty TargetMacro where
  prettyM PointerAlignment = "pointerAlignment"
