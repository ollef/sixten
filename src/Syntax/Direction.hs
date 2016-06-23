{-# LANGUAGE OverloadedStrings #-}
module Syntax.Direction where

import Syntax.Pretty

data Direction = Direct | Indirect
  deriving (Eq, Ord, Show)

instance Pretty Direction where
  prettyM Direct = "direct"
  prettyM Indirect = "indirect"
