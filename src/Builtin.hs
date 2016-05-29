{-# LANGUAGE OverloadedStrings, ViewPatterns, PatternSynonyms #-}
module Builtin where

import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import Data.String
import Data.Void

import Syntax
import Syntax.Abstract as Abstract

pattern SizeName <- ((==) "Size" -> True) where SizeName = "Size"
pattern Size = Global SizeName

pattern AddSizeName <- ((==) "+" -> True) where AddSizeName = "+"
pattern AddSize e1 e2 = App (App (Global AddSizeName) ReEx e1) ReEx e2

pattern MaxSizeName <- ((==) "max" -> True) where MaxSizeName = "max"
pattern MaxSize e1 e2 = App (App (Global MaxSizeName) ReEx e1) ReEx e2

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type sz = App (Global TypeName) IrIm sz

pattern IndArgTypeName <- ((==) "IndArg" -> True) where IndArgTypeName = "IndArg"
pattern IndArgType sz t = App (App (Global IndArgTypeName) IrIm sz) IrEx t

pattern IndRetTypeName <- ((==) "IndRet" -> True) where IndRetTypeName = "IndRet"
pattern IndRetType sz t = App (App (Global IndRetTypeName) IrIm sz) IrEx t

pattern IndArgName <- ((==) "indArg" -> True) where IndArgName = "indArg"
pattern IndArg sz t a = App (App (App (Global IndArgName) ReIm sz) IrIm t) ReEx a

pattern IndRetName <- ((==) "indRet" -> True) where IndRetName = "indRet"
pattern IndRet sz t a = App (App (App (Global IndRetName) ReIm sz) IrIm t) ReEx a

pattern RefName <- ((==) "Ref" -> True) where RefName = "Ref"
pattern PtrName <- ((==) "Ptr" -> True) where PtrName = "Ptr"

apply :: Int -> Name
apply n = "apply_" `mappend` fromString (show n)

closure :: QConstr
closure = QConstr "Builtin" "CL"

context :: Program Expr Void
context = HM.fromList
  [ (SizeName, opaque $ Type $ Lit 1)
  , (AddSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (MaxSizeName, opaque $ arrow ReEx Size $ arrow ReEx Size Size)
  , (TypeName, opaque $ arrow IrIm Size $ Type $ Lit 0)
  , (PtrName, dataType (Abstract.pi_ "size" IrIm Size
                       $ arrow IrEx (Type $ pure "size")
                       $ Type $ Lit 1)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow ReEx (pure 1)
                                           $ apps (Global PtrName) [(IrIm, pure 0), (IrEx, pure 1)]
                       ])
  -- , (IndArgTypeName, opaque $ Abstract.pi_ "size" IrIm Size
  --                           $ arrow IrEx (Type $ pure "size")
  --                           $ Type $ Lit 1)
  -- , (IndRetTypeName, opaque $ Abstract.pi_ "size" IrIm Size
  --                           $ arrow IrEx (Type $ pure "size")
  --                           $ Type $ Lit 1)
  -- , (IndRetName, opaque $ Abstract.pi_ "size" ReIm Size
  --                       $ Abstract.pi_ "t" IrIm (Type $ pure "size")
  --                       $ arrow ReEx (Type $ pure "t")
  --                       $ IndRetType (pure "size") (pure "t"))
  -- , (IndArgName, opaque $ Abstract.pi_ "size" ReIm Size
  --                       $ Abstract.pi_ "t" IrIm (Type $ pure "size")
  --                       $ arrow ReEx (Type $ pure "t")
  --                       $ IndArgType (pure "size") (pure "t"))
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
