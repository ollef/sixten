{-# LANGUAGE PatternSynonyms, PolyKinds, TypeFamilies, OverloadedStrings #-}
module Syntax.Annotation where

import Pretty

class Eq a => PrettyAnnotation a where
  prettyAnnotation :: a -> PrettyM Doc -> PrettyM Doc
  prettyAnnotationParens :: a -> PrettyM Doc -> PrettyM Doc
  prettyAnnotationParens p = prettyAnnotation p . parens

class Annotated (e :: k) where
  type Annotation e :: *

instance PrettyAnnotation () where
  prettyAnnotation _ = id

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord)

instance Show Plicitness where
  show Implicit = "Im"
  show Explicit = "Ex"

instance PrettyAnnotation Plicitness where
  prettyAnnotation p = braces `iff` (p == Implicit)
  prettyAnnotationParens Implicit = braces
  prettyAnnotationParens Explicit = parens

data Erasability = Erased | Zeroed | Retained
  deriving (Eq, Ord)

instance Show Erasability where
  show Erased = "Er"
  show Zeroed = "Ze"
  show Retained = "Re"

instance PrettyAnnotation Erasability where
  prettyAnnotation Erased = prettyTightApp "~"
  prettyAnnotation Zeroed = prettyTightApp "0~"
  prettyAnnotation Retained = id

data Visibility = Private | Public
  deriving (Eq, Ord, Show)

instance Pretty Visibility where
  prettyM Private = "private"
  prettyM Public = "public"
