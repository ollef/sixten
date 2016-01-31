{-# LANGUAGE OverloadedStrings #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM
import Data.Maybe

import Syntax
import Syntax.Abstract
import Util

size :: Name
size = "Size"

sizeE :: Expr d a
sizeE = Global size

addSize :: Name
addSize = "+"

addSizeE :: d -> Expr d a -> Expr d a -> Expr d a
addSizeE d e1 e2 = apps (Global addSize) [(d, e1), (d, e2)]

maxSize :: Name
maxSize = "max"

maxSizeE :: d -> Expr d a -> Expr d a -> Expr d a
maxSizeE d e1 e2 = apps (Global maxSize) [(d, e1), (d, e2)]

type_ :: Name
type_ = "Type"

typeE :: d -> Expr d a -> Expr d a
typeE = App (Global type_)

typeN :: d -> Integer -> Expr d a
typeN d = typeE d . Lit

pointer :: Name
pointer = "Ptr"

ref :: Constr
ref = "Ref"

context :: Program Annotation (Expr Annotation) Empty
context = HM.fromList
  [ (size, opaque $ typeN ie 1)
  , (addSize, opaque $ arrow ie sizeE $ arrow ie sizeE sizeE)
  , (maxSize, opaque $ arrow ie sizeE $ arrow ie sizeE sizeE)
  , (type_, opaque $ arrow ie sizeE $ typeN ie 0)
  , (pointer, dataType (pi_ "size" ii sizeE $ arrow ie (typeE ie $ pure "size") $ typeN ie 1)
                       [ ConstrDef ref $ toScope $ fmap B $ arrow re (pure 1)
                                       $ apps (Global pointer) [(ii, pure 0), (ie, pure 1)]
                       ])
  ]
  where
    ie = Annotation Irrelevant Explicit
    re = Annotation Relevant Explicit
    ii = Annotation Irrelevant Implicit
    ri = Annotation Relevant Implicit
    opaque
      :: Expr Annotation Name
      -> ( Definition (Expr Annotation) Empty
         , Expr Annotation Empty
         , Annotation)
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t =
      ( DataDefinition $ DataDef mempty
      , cl t
      , ie
      )
    dataType t xs =
      ( DataDefinition $ DataDef xs
      , cl t
      , ie
      )
