{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings #-}
module Syntax.Direction where

import Data.Vector(Vector)

import Pretty
import Syntax.Annotation
import Syntax.Extern
import Syntax.Module
import TypeRep

data Direction = Direct TypeRep | Indirect
  deriving (Eq, Ord, Show)

instance Pretty Direction where
  prettyM (Direct rep) = "direct(" <> prettyM rep <> ")"
  prettyM Indirect = "indirect"

instance PrettyAnnotation Direction where
  prettyAnnotation (Direct rep) = prettyTightApp (prettyM rep <> "~")
  prettyAnnotation Indirect = prettyTightApp "&"

data ReturnDirection a
  = ReturnDirect TypeRep
  | ReturnIndirect a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Pretty a => Pretty (ReturnDirection a) where
  prettyM (ReturnDirect sz) = "direct(" <> prettyM sz <> ")"
  prettyM (ReturnIndirect a) = "indirect" <+> prettyM a

instance PrettyAnnotation a => PrettyAnnotation (ReturnDirection a) where
  prettyAnnotation (ReturnDirect rep) = prettyTightApp (prettyM rep <> "~")
  prettyAnnotation (ReturnIndirect a) = prettyAnnotation a

data ReturnIndirect
  = Projection
  | OutParam
  deriving (Eq, Ord, Show)

instance PrettyAnnotation ReturnIndirect where
  prettyAnnotation Projection = prettyTightApp "*"
  prettyAnnotation OutParam = prettyTightApp "&"

instance Pretty ReturnIndirect where
  prettyM OutParam = "outparam"
  prettyM Projection = "projection"

type RetDir = ReturnDirection ReturnIndirect

toReturnDirection :: d -> Direction -> ReturnDirection d
toReturnDirection _ (Direct sz) = ReturnDirect sz
toReturnDirection d Indirect = ReturnIndirect d

data ClosureDir
  = NonClosureDir Direction
  | ClosureDir
  deriving (Eq, Ord, Show)

instance PrettyAnnotation ClosureDir where
  prettyAnnotation (NonClosureDir dir) = prettyAnnotation dir
  prettyAnnotation ClosureDir = prettyTightApp "[]"

instance Pretty ClosureDir where
  prettyM (NonClosureDir d) = prettyM d
  prettyM ClosureDir = "closure"

-- | Should the name be mangled and calling convention be adjusted to be C-compatible?
data Compatibility
  = CompatibleWith Language
  | SixtenCompatible
  deriving (Eq, Ord, Show)

data Signature a
  = FunctionSig Compatibility (ReturnDirection a) (Vector Direction)
  | ConstantSig Direction
  | AliasSig QName
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
