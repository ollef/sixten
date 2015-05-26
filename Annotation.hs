module Annotation where

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord, Show)

class HasPlicitness d where
  plicitness :: d -> Plicitness

isImplicit, isExplicit :: HasPlicitness d => d -> Bool
isImplicit = (== Implicit) . plicitness
isExplicit = (== Explicit) . plicitness

instance HasPlicitness Plicitness where
  plicitness = id

data Relevance = Irrelevant | Relevant
  deriving (Eq, Ord, Show)

class HasRelevance d where
  relevance :: d -> Relevance

isIrrelevant, isRelevant :: HasRelevance d => d -> Bool
isIrrelevant = (== Irrelevant) . relevance
isRelevant   = (== Relevant)   . relevance

instance HasRelevance Relevance where
  relevance = id

instance HasRelevance Plicitness where
  relevance _ = Relevant

data Annotation = Annotation Relevance Plicitness
  deriving (Eq, Ord, Show)

instance HasRelevance Annotation where
  relevance (Annotation r _) = r

instance HasPlicitness Annotation where
  plicitness (Annotation _ p) = p
