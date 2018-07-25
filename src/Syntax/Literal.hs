{-# LANGUAGE OverloadedStrings #-}
module Syntax.Literal where

import Data.Word
import qualified TypeRep

import Pretty

data Literal
  = Integer !Integer
  | Byte !Word8
  | TypeRep !TypeRep.TypeRep
  deriving (Eq, Ord, Show)

instance Pretty Literal where
  prettyM (Integer i) = prettyM i
  prettyM (Byte i) = "(Byte)" <> prettyM (fromIntegral i :: Integer)
  prettyM (TypeRep tr) = prettyM tr
