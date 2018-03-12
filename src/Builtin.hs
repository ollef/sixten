{-# LANGUAGE OverloadedStrings, MonadComprehensions #-}
module Builtin where

import Control.Applicative
import Data.Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List.NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Backend.Target(Target)
import Builtin.Names
import Syntax
import Syntax.Abstract as Abstract
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import qualified TypeRep
import Util

context :: Target -> HashMap QName (Definition Expr Void, Type Void)
context target = HashMap.fromList
  [ (TypeName, dataType typeRep Type [])
  , (PtrName, dataType
      (Lam mempty Explicit Type $ Scope ptrRep)
      (arrow Explicit Type Type)
      [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
        $ Abstract.App (Global PtrName) Explicit (pure 0)
      ])
  , (IntName, opaqueData intRep Type)
  , (NatName, dataType intRep Type
      [ ConstrDef ZeroName $ Scope Nat
      , ConstrDef SuccName $ Scope $ arrow Explicit Nat Nat
      ])
  , (PiTypeName, opaqueData ptrRep Type)
  ]
  where
    cl = fromMaybe (error "Builtin not closed") . closed
    -- TODO: Should be made nonmatchable
    opaqueData rep t = dataType rep t mempty
    dataType rep t xs = (DataDefinition (DataDef xs) rep, cl t)

    intRep = MkType $ TypeRep.intRep target
    ptrRep = MkType $ TypeRep.ptrRep target
    typeRep = MkType $ TypeRep.typeRep target

convertedContext :: Target -> HashMap QName (Sized.Definition Lifted.Expr Void)
convertedContext target = HashMap.fromList $ concat
  [ [(papName left given, pap target left given)
    | given <- [1..maxArity - 1], left <- [1..maxArity - given]
    ]
  , [(applyName arity, apply target arity)
    | arity <- [1..maxArity]
    ]
  ]

convertedSignatures :: Target -> HashMap QName Lifted.FunSignature
convertedSignatures target
  = flip HashMap.mapMaybe (convertedContext target) $ \def ->
    case def of
      Sized.FunctionDef _ _ (Sized.Function tele (AnnoScope _ s)) -> Just (tele, s)
      Sized.ConstantDef _ _ -> Nothing
      Sized.AliasDef -> Nothing

deref :: Lifted.Expr v -> Lifted.Expr v
deref e
  = Lifted.Case (Anno e unknownSize)
  $ ConBranches
  $ pure
  $ ConBranch
    Ref
    (Telescope $ pure $ TeleArg "dereferenced" () $ Scope unknownSize)
    (toScope $ pure $ B 0)
  where
    unknownSize = global "Sixten.Builtin.deref.unknownSize"

maxArity :: Num n => n
maxArity = 6

apply :: Target -> Int -> Sized.Definition Lifted.Expr Void
apply target numArgs
  = Sized.FunctionDef Public Sized.NonClosure
  $ Sized.Function
    (Telescope
    $ Vector.cons (TeleArg "this" () $ Scope ptrRep)
    $ (\n -> TeleArg (fromText $ "type" <> shower (unTeleVar n)) () $ Scope typeRep) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> TeleArg (fromText $ "x" <> shower (unTeleVar n)) () $ Scope $ pure $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs)
  $ toAnnoScope
  $ flip Anno unknownSize
  $ Lifted.Case (Anno (deref $ pure $ B 0) unknownSize)
  $ ConBranches
  $ pure
  $ ConBranch
    Closure
    (Telescope $ Vector.fromList
      [TeleArg "f_unknown" () $ Scope ptrRep, TeleArg "n" () $ Scope intRep])
    (toScope
      $ Lifted.Case (Anno (pure $ B 1) unknownSize)
      $ LitBranches
        [LitBranch (Integer $ fromIntegral arity) $ br arity | arity <- 1 :| [2..maxArity]]
        $ Lifted.Call (global FailName) $ pure $ Anno unitRep typeRep)
  where
    unitRep = Lifted.MkType TypeRep.UnitRep
    intRep = Lifted.MkType $ TypeRep.intRep target
    ptrRep = Lifted.MkType $ TypeRep.ptrRep target
    typeRep = Lifted.MkType $ TypeRep.typeRep target
    unknownSize = global "Sixten.Builtin.apply.unknownSize"

    directPtr = Direct $ TypeRep.ptrRep target
    directType = Direct $ TypeRep.typeRep target

    br :: Int -> Lifted.Expr (Var TeleVar (Var TeleVar Void))
    br arity
      | numArgs < arity
        = Lifted.Con Ref
        $ pure
        $ sizedCon target (Lifted.MkType TypeRep.UnitRep) Closure
        $ Vector.cons (Anno (global $ papName (arity - numArgs) numArgs) ptrRep)
        $ Vector.cons (Anno (Lifted.Lit $ Integer $ fromIntegral $ arity - numArgs) intRep)
        $ Vector.cons (Anno (pure $ F $ B 0) ptrRep)
        $ (\n -> Anno (pure $ F $ B $ 1 + n) typeRep) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> Anno (pure $ F $ B $ 1 + TeleVar numArgs + n) (pure $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Lifted.PrimCall (ReturnIndirect OutParam) (pure $ B 0)
        $ Vector.cons (directPtr, Anno (pure $ F $ B 0) ptrRep)
        $ (\n -> (directType, Anno (pure $ F $ B $ 1 + n) typeRep)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Indirect, Anno (pure $ F $ B $ 1 + TeleVar numArgs + n) (pure $ F $ B $ 1 + n))) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Lifted.Call (global $ applyName $ numArgs - arity)
        $ Vector.cons
          (flip Anno ptrRep
          $ Lifted.PrimCall (ReturnIndirect OutParam) (pure $ B 0)
          $ Vector.cons (directPtr, Anno (pure $ F $ B 0) ptrRep)
          $ (\n -> (directType, Anno (pure $ F $ B $ 1 + n) typeRep)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Indirect, Anno (pure $ F $ B $ 1 + fromIntegral numArgs + n) (pure $ F $ B $ 1 + n))) <$> Vector.enumFromN 0 arity)
        $ (\n -> Anno (pure $ F $ B $ 1 + n) typeRep) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> Anno (pure $ F $ B $ 1 + fromIntegral numArgs + n) (pure $ F $ B $ 1 + n)) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

pap :: Target -> Int -> Int -> Sized.Definition Lifted.Expr Void
pap target k m
  = Sized.FunctionDef Public Sized.NonClosure
  $ Sized.Function
    (Telescope
    $ Vector.cons (TeleArg "this" () $ Scope ptrRep)
    $ (\n -> TeleArg (fromText $ "type" <> shower (unTeleVar n)) () $ Scope typeRep) <$> Vector.enumFromN 0 k
    <|> (\n -> TeleArg (fromText $ "x" <> shower (unTeleVar n)) () $ Scope $ pure $ B $ 1 + n) <$> Vector.enumFromN 0 k)
  $ toAnnoScope
  $ flip Anno unknownSize
  $ Lifted.Case (Anno (deref $ pure $ B 0) unknownSize)
  $ ConBranches
  $ pure
  $ ConBranch
    Closure
    (Telescope
      $ Vector.cons (TeleArg "_" () $ Scope ptrRep)
      $ Vector.cons (TeleArg "_" () $ Scope intRep)
      $ Vector.cons (TeleArg "that" () $ Scope ptrRep)
      $ (\n -> TeleArg (fromText $ "type" <> shower (unTeleVar n)) () $ Scope typeRep) <$> Vector.enumFromN 0 m
      <|> (\n -> TeleArg (fromText $ "y" <> shower (unTeleVar n)) () $ Scope $ pure $ B $ 3 + n) <$> Vector.enumFromN 0 m)
    (toScope
      $ Lifted.Call (global $ applyName $ m + k)
      $ Vector.cons (Anno (pure $ B 2) ptrRep)
      $ (\n -> Anno (pure $ B $ 3 + n) typeRep) <$> Vector.enumFromN 0 m
      <|> (\n -> Anno (pure $ F $ B $ 1 + n) typeRep) <$> Vector.enumFromN 0 k
      <|> (\n -> Anno (pure $ B $ 3 + TeleVar m + n) (pure $ B $ 3 + n)) <$> Vector.enumFromN 0 m
      <|> (\n -> Anno (pure $ F $ B $ 1 + TeleVar k + n) (pure $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 k
    )
  where
    unknownSize = global "Sixten.Builtin.pap.unknownSize"
    intRep = Lifted.MkType $ TypeRep.intRep target
    ptrRep = Lifted.MkType $ TypeRep.ptrRep target
    typeRep = Lifted.MkType $ TypeRep.typeRep target

sizedCon :: Target -> Lifted.Expr v -> QConstr -> Vector (Anno Lifted.Expr v) -> Anno Lifted.Expr v
sizedCon target tagRep qc args
  = Anno (Lifted.Con qc args) (productTypes target $ Vector.cons tagRep argTypes)
  where
    argTypes = typeAnno <$> args

productType :: Target -> Lifted.Expr v -> Lifted.Expr v -> Lifted.Expr v
productType _ a (Lifted.MkType TypeRep.UnitRep) = a
productType _ (Lifted.MkType TypeRep.UnitRep) b = b
productType _ (Lifted.MkType rep1) (Lifted.MkType rep2) = Lifted.MkType $ TypeRep.product rep1 rep2
productType target a b
  = Lifted.Call (global ProductTypeRepName)
  $ Vector.fromList [Anno a (Lifted.MkType typeRep), Anno b (Lifted.MkType typeRep)]
  where
     typeRep = TypeRep.typeRep target

productTypes :: Target -> Vector (Lifted.Expr v) -> Lifted.Expr v
productTypes target = foldl' (productType target) (Lifted.MkType TypeRep.UnitRep)
