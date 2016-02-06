{-# LANGUAGE OverloadedStrings, ViewPatterns, PatternSynonyms #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM
import Data.Maybe

import Syntax
import Syntax.Abstract
import Util

pattern SizeName <- ((==) "Size" -> True) where SizeName = "Size"
pattern Size = Global SizeName

pattern AddSizeName <- ((==) "+" -> True) where AddSizeName = "+"
pattern AddSize e1 e2 = App (App (Global AddSizeName) ReEx e1) ReEx e2

pattern MaxSizeName <- ((==) "max" -> True) where MaxSizeName = "max"
pattern MaxSize e1 e2 = App (App (Global MaxSizeName) ReEx e1) ReEx e2

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type sz = App (Global TypeName) IrIm sz

pointer :: Name
pointer = "Ptr"

ref :: Constr
ref = "Ref"

context :: Program Expr Empty
context = HM.fromList
  [ (SizeName, opaque $ Type $ Lit 1)
  , (AddSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (MaxSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (TypeName, opaque $ arrow IrIm Size $ Type $ Lit 0)
  , (pointer, dataType (pi_ "size" IrIm Size $ arrow IrEx (Type $ pure "size") $ Type $ Lit 1)
                       [ ConstrDef ref $ toScope $ fmap B $ arrow ReEx (pure 1)
                                       $ apps (Global pointer) [(IrIm, pure 0), (IrEx, pure 1)]
                       ])
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
