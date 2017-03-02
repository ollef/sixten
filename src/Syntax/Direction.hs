{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings #-}
module Syntax.Direction where

import Pretty
import Syntax.Annotation

data Direction = Void | Direct | Indirect
  deriving (Eq, Ord, Show)

instance Pretty Direction where
  prettyM Void = "void"
  prettyM Direct = "direct"
  prettyM Indirect = "indirect"

instance PrettyAnnotation Direction where
  prettyAnnotation Void = prettyTightApp "0~"
  prettyAnnotation Direct = id
  prettyAnnotation Indirect = prettyTightApp "&"

data ReturnDirection a
  = ReturnVoid
  | ReturnDirect
  | ReturnIndirect a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Pretty a => Pretty (ReturnDirection a) where
  prettyM ReturnVoid = "void"
  prettyM ReturnDirect = "direct"
  prettyM (ReturnIndirect a) = "indirect" <+> prettyM a

instance PrettyAnnotation a => PrettyAnnotation (ReturnDirection a) where
  prettyAnnotation ReturnVoid = prettyTightApp "0~"
  prettyAnnotation ReturnDirect = id
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
toReturnDirection _ Void = ReturnVoid
toReturnDirection _ Direct = ReturnDirect
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
