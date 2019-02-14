{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax.Literal where

import Protolude

import Numeric.Natural

import Pretty
import qualified TypeRep

data Literal
  = Integer !Integer
  | Natural !Natural
  | Byte !Word8
  | TypeRep !TypeRep.TypeRep
  deriving (Eq, Ord, Show, Generic, Hashable)

instance Pretty Literal where
  prettyM (Integer i) = prettyM i
  prettyM (Natural n) = "(Nat)" <> prettyM n
  prettyM (Byte i) = "(Byte)" <> prettyM (fromIntegral i :: Integer)
  prettyM (TypeRep tr) = prettyM tr
