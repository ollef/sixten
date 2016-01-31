{-# LANGUAGE OverloadedStrings #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM
import Data.Maybe

import Syntax
import Syntax.Abstract
import Util

size :: Name
size = "Size"

sizeE :: Expr a
sizeE = Global size

addSize :: Name
addSize = "+"

addSizeE :: Expr a -> Expr a -> Expr a
addSizeE e1 e2 = apps (Global addSize) [(Explicit, e1), (Explicit, e2)]

maxSize :: Name
maxSize = "max"

maxSizeE :: Expr a -> Expr a -> Expr a
maxSizeE e1 e2 = apps (Global maxSize) [(Explicit, e1), (Explicit, e2)]

type_ :: Name
type_ = "Type"

typeE :: Expr a -> Expr a
typeE = App (Global type_) Explicit

typeN :: Integer -> Expr a
typeN = typeE . Lit

pointer :: Name
pointer = "Ptr"

ref :: Constr
ref = "Ref"

context :: Program Expr Empty
context = HM.fromList
  [ (size, opaque $ typeN 1)
  , (addSize, opaque $ arrow Explicit sizeE $ arrow Explicit sizeE sizeE)
  , (maxSize, opaque $ arrow Explicit sizeE $ arrow Explicit sizeE sizeE)
  , (type_, opaque $ arrow Explicit sizeE $ typeN 0)
  , (pointer, dataType (pi_ "size" Implicit sizeE $ arrow Explicit (typeE $ pure "size") $ typeN 1)
                       [ ConstrDef ref $ toScope $ fmap B $ arrow Explicit (pure 1)
                                       $ apps (Global pointer) [(Implicit, pure 0), (Explicit, pure 1)]
                       ])
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
