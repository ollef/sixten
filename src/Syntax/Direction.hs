{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, OverloadedStrings #-}
module Syntax.Direction where

import Syntax.Pretty

data Direction = Void | Direct | Indirect
  deriving (Eq, Ord, Show)

instance Pretty Direction where
  prettyM Void = "void"
  prettyM Direct = "direct"
  prettyM Indirect = "indirect"

data ReturnDirection a
  = ReturnVoid
  | ReturnDirect
  | ReturnIndirect a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Pretty a => Pretty (ReturnDirection a) where
  prettyM ReturnVoid = "void"
  prettyM ReturnDirect = "direct"
  prettyM (ReturnIndirect a) = "indirect" <+> prettyM a

data ReturnIndirect
  = Projection
  | OutParam
  deriving (Eq, Ord, Show)

instance Pretty ReturnIndirect where
  prettyM OutParam = "outparam"
  prettyM Projection = "projection"

type RetDir = ReturnDirection ReturnIndirect

toReturnDirection :: d -> Direction -> ReturnDirection d
toReturnDirection _ Void = ReturnVoid
toReturnDirection _ Direct = ReturnDirect
toReturnDirection d Indirect = ReturnIndirect d

