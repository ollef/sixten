{-# LANGUAGE PatternSynonyms, PolyKinds, TypeFamilies, OverloadedStrings #-}
module Syntax.Annotation where

import Pretty

class Eq a => PrettyAnnotation a where
  prettyAnnotation :: a -> PrettyM Doc -> PrettyM Doc
  prettyAnnotationParens :: a -> PrettyM Doc -> PrettyM Doc
  prettyAnnotationParens p = prettyAnnotation p . parens

instance PrettyAnnotation () where
  prettyAnnotation _ = id

data Plicitness = Constraint | Implicit | Explicit
  deriving (Eq, Ord)

instance Show Plicitness where
  show Constraint = "Co"
  show Implicit = "Im"
  show Explicit = "Ex"

instance PrettyAnnotation Plicitness where
  prettyAnnotation Constraint = brackets
  prettyAnnotation Implicit = braces
  prettyAnnotation Explicit = id
  prettyAnnotationParens Constraint = brackets
  prettyAnnotationParens Implicit = braces
  prettyAnnotationParens Explicit = parens

data Visibility = Private | Public
  deriving (Eq, Ord, Show)

instance Pretty Visibility where
  prettyM Private = "private"
  prettyM Public = "public"

data Abstract = Abstract | Concrete
  deriving (Eq, Ord, Show)

instance Pretty Abstract where
  prettyM Abstract = "abstract"
  prettyM Concrete = "concrete"

data IsInstance
  = IsOrdinaryDefinition
  | IsInstance
  deriving (Eq, Ord, Show)

instance Pretty IsInstance where
  prettyM IsOrdinaryDefinition = mempty
  prettyM IsInstance = "instance"
