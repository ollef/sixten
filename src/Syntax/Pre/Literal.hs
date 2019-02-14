{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Syntax.Pre.Literal where

import Protolude

import Data.Text(Text)

import Pretty

data Literal
  = Integer !Integer
  | String !Text
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Pretty Literal where
  prettyM (Integer i) = prettyM i
  prettyM (String s) = prettyM s
