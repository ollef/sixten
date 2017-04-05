{-# LANGUAGE OverloadedStrings #-}
module Syntax.Literal where

import Data.Word
import Data.Monoid

import Pretty

data Literal
  = Integer Integer
  | Byte Word8
  deriving (Eq, Ord, Show)

instance Pretty Literal where
  prettyM (Integer i) = prettyM i
  prettyM (Byte i) = "(Byte)" <> prettyM (fromIntegral i :: Integer)
