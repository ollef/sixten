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

pattern AddSizeName <- ((==) "addSize" -> True) where AddSizeName = "addSize"
pattern AddSize e1 e2 = App (App (Global AddSizeName) ReEx e1) ReEx e2

pattern MaxSizeName <- ((==) "maxSize" -> True) where MaxSizeName = "maxSize"
pattern MaxSize e1 e2 = App (App (Global MaxSizeName) ReEx e1) ReEx e2

pattern TypeName <- ((==) "Type" -> True) where TypeName = "Type"
pattern Type sz = App (Global TypeName) IrIm sz

pattern RefName <- ((==) "Ref" -> True) where RefName = "Ref"
pattern PtrName <- ((==) "Ptr" -> True) where PtrName = "Ptr"

pattern DerefName <- ((==) "deref" -> True) where DerefName = "deref"

pattern Closure <- ((== QConstr "Builtin" "CL") -> True) where Closure = QConstr "Builtin" "CL"

pattern Ref <- ((== QConstr PtrName RefName) -> True) where Ref = QConstr PtrName RefName

apply :: Int -> Name
apply n = "apply_" `mappend` fromString (show n)

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
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    opaque t = (DataDefinition $ DataDef mempty, cl t)
    dataType t xs = (DataDefinition $ DataDef xs, cl t)
