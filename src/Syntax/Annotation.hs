{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module Syntax.Annotation where

import Syntax.Pretty

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord)

instance Show Plicitness where
  show Implicit = "Im"
  show Explicit = "Ex"

data Relevance = Irrelevant | Relevant
  deriving (Eq, Ord)

instance Show Relevance where
  show Relevant = "Re"
  show Irrelevant = "Ir"

data Annotation = Annotation
  { relevance :: Relevance
  , plicitness :: Plicitness
  } deriving (Eq, Ord)

instance Show Annotation where
  show (Annotation r p) = show r ++ show p

prettyAnnotation :: Annotation -> PrettyM Doc -> PrettyM Doc
prettyAnnotation a
  = (prettyTightApp (pure tilde) `iff` (relevance a == Irrelevant))
  . (braces `iff` (plicitness a == Implicit))

prettyAnnotationParens :: Annotation -> PrettyM Doc -> PrettyM Doc
prettyAnnotationParens a
  = (prettyTightApp (pure tilde) `iff` (relevance a == Irrelevant))
  . (if plicitness a == Implicit then braces else parens)

pattern ReEx = Annotation Relevant Explicit
pattern IrEx = Annotation Irrelevant Explicit
pattern ReIm = Annotation Relevant Implicit
pattern IrIm = Annotation Irrelevant Implicit

data Visibility = Private | Public
  deriving (Eq, Ord, Show)

instance Pretty Visibility where
  prettyM Private = "private"
  prettyM Public = "public"
