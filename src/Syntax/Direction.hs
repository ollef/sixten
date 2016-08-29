{-# LANGUAGE OverloadedStrings #-}
module Syntax.Direction where

import Syntax.Pretty

data Direction = Void | Direct | Indirect
  deriving (Eq, Ord, Show)

instance Pretty Direction where
  prettyM Void = "void"
  prettyM Direct = "direct"
  prettyM Indirect = "indirect"
