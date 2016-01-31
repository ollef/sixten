{-# LANGUAGE OverloadedStrings #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM
import Data.Maybe

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

type_ :: Name
type_ = "Type"

typeE :: d -> Expr d a -> Expr d a
typeE = App (Global type_)

typeN :: d -> Integer -> Expr d a
typeN d = typeE d . Lit

pointer :: Name
pointer = "Ptr"

context :: Program Annotation (Expr Annotation) Empty
context = HM.fromList
  [ (int, opaque $ typeN ie 1)
  , (add, opaque $ arrow ie intE $ arrow ie intE intE)
  , (max_, opaque $ arrow ie intE $ arrow ie intE intE)
  , (type_, opaque $ arrow ie intE $ typeN ie 0)
  , (pointer, opaque $ pi_ "size" ii intE
                     $ arrow ie (typeE ie (pure "size")) $ typeN ie 1)
  ]
  where
    ie = Annotation Irrelevant Explicit
    ii = Annotation Irrelevant Implicit
    opaque
      :: Expr Annotation Name
      -> ( Definition (Expr Annotation) Empty
         , Expr Annotation Empty
         , Annotation)
    opaque t =
      ( DataDefinition $ DataDef mempty
      , fromMaybe (error "Builtin not closed") $ closed t
      , ie
      )
