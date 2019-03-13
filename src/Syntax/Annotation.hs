{-# LANGUAGE DeriveGeneric, PatternSynonyms, PolyKinds, TypeFamilies, OverloadedStrings #-}
module Syntax.Annotation where

import qualified Prelude(show)

import Protolude

import Pretty

class Eq a => PrettyAnnotation a where
  prettyAnnotation :: a -> PrettyDoc -> PrettyDoc
  prettyAnnotationParens :: a -> PrettyDoc -> PrettyDoc
  prettyAnnotationParens p = prettyAnnotation p . parens

data Plicitness = Constraint | Implicit | Explicit
  deriving (Eq, Ord, Generic)

implicitise :: Plicitness -> Plicitness
implicitise Constraint = Constraint
implicitise Implicit = Implicit
implicitise Explicit = Implicit

instance Hashable Plicitness where

instance Show Plicitness where
  show Constraint = "Co"
  show Implicit = "Im"
  show Explicit = "Ex"

instance PrettyAnnotation Plicitness where
  prettyAnnotation Constraint = brackets
  prettyAnnotation Implicit = prettyTightApp "@"
  prettyAnnotation Explicit = identity
  prettyAnnotationParens Constraint = brackets
  prettyAnnotationParens Implicit = prettyTightApp "@" . parens
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

data Boxiness = Boxed | Unboxed
  deriving (Eq, Ord, Show)

instance Pretty Boxiness where
  prettyM Boxed = "boxed"
  prettyM Unboxed = "unboxed"
