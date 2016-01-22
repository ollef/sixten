{-# LANGUAGE OverloadedStrings #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM

import Syntax
import Syntax.Abstract
import Util

int :: Name
int = "Int"

intE :: Expr d a
intE = Global int

add :: Name
add = "+"

addE :: d -> Expr d a -> Expr d a -> Expr d a
addE d e1 e2 = apps (Global add) [(d, e1), (d, e2)]

max_ :: Name
max_ = "max"

maxE :: d -> Expr d a -> Expr d a -> Expr d a
maxE d e1 e2 = apps (Global max_) [(d, e1), (d, e2)]

sizeOf :: Name
sizeOf = "sizeOf" -- : forall {n}. Type n -> Int

sizeOfE :: d -> Expr d a -> Expr d a
sizeOfE d = App (Global sizeOf) d

type_ :: Name
type_ = "Type"

typeE :: d -> Expr d a -> Expr d a
typeE d = App (Global type_) d

typeN :: d -> Integer -> Expr d a
typeN d = typeE d . Lit

context :: Program Annotation (Expr Annotation) Empty
context = HM.fromList
  [ (int, opaque $ typeN irr 1)
  , (add, opaque $ arrow irr intE $ arrow irr intE intE)
  , (max_, opaque $ arrow irr intE $ arrow irr intE intE)
  , (type_, opaque $ arrow irr intE $ typeN irr 0)
  ]
  where
    irr = Annotation Irrelevant Explicit
    opaque t = (DataDefinition $ DataDef mempty, t, irr)
