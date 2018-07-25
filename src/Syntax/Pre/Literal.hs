module Syntax.Pre.Literal where

import Data.Text(Text)

import Pretty

data Literal
  = Integer !Integer
  | String !Text
  deriving (Eq, Ord, Show)

instance Pretty Literal where
  prettyM (Integer i) = prettyM i
  prettyM (String s) = prettyM s
