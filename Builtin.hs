{-# LANGUAGE OverloadedStrings #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM

import Annotation
import Core
import Data
import Definition
import Util

int :: Expr a v
int = Global "Int"

context :: Program (Expr Annotation) Annotation Empty
context = HM.fromList
  [ ("Int", opaque)
  ]
  where
    opaque = (DataDefinition $ DataDef mempty mempty, Type, Annotation Irrelevant Explicit)

