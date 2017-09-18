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
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import qualified TypeRep
import Util

context :: Target -> HashMap QName (Definition Expr Void, Type Void)
context target = HashMap.fromList
  [ (TypeName, opaqueData typeRep Type)
  , (PtrName, dataType (Lam mempty Explicit Type $ Scope ptrRep)
                       (arrow Explicit Type Type)
                       [ ConstrDef RefName $ toScope $ fmap B $ arrow Explicit (pure 0)
                                           $ app (Global PtrName) Explicit (pure 0)
                       ])
  , (ByteName, opaqueData byteRep Type)
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

    byteRep = Lit $ TypeRep TypeRep.byte
    intRep = Lit $ TypeRep $ TypeRep.int target
    ptrRep = Lit $ TypeRep $ TypeRep.ptr target
    typeRep = Lit $ TypeRep $ TypeRep.typeRep target

convertedContext :: Target -> HashMap QName (Sized.Definition Lifted.Expr Void)
convertedContext target = HashMap.fromList $ concat
  [[( TypeName
    , constDef $ Lifted.Sized typeRep typeRep
    )
  , ( PiTypeName
    , constDef $ Lifted.Sized typeRep ptrRep
    )
  , ( PtrName
    , funDef (Telescope $ pure (TeleArg mempty () $ Scope typeRep))
      $ Scope $ Lifted.Sized typeRep ptrRep
    )
  , ( IntName
    , constDef $ Lifted.Sized typeRep intRep
    )
  , ( ByteName
    , constDef $ Lifted.Sized typeRep byteRep
    )
  ]
  , [(papName left given, pap target left given) | given <- [1..maxArity - 1], left <- [1..maxArity - given]]
  , [(applyName arity, apply target arity) | arity <- [1..maxArity]]
  ]
  where
    constDef = Sized.ConstantDef Public . Sized.Constant
    funDef tele = Sized.FunctionDef Public Sized.NonClosure . Sized.Function tele

    intRep = Lifted.Lit $ TypeRep $ TypeRep.int target
    typeRep = Lifted.Lit $ TypeRep $ TypeRep.typeRep target
    byteRep = Lifted.Lit $ TypeRep TypeRep.byte
    ptrRep = Lifted.Lit $ TypeRep $ TypeRep.ptr target

convertedSignatures :: Target -> HashMap QName Lifted.FunSignature
convertedSignatures target
  = flip HashMap.mapMaybeWithKey (convertedContext target) $ \name def ->
    case def of
      Sized.FunctionDef _ _ (Sized.Function tele s) -> case fromScope s of
        Lifted.Anno _ t -> Just (tele, toScope t)
        _ -> error $ "Sixten.Builtin.convertedSignatures " <> show name
      Sized.ConstantDef _ _ -> Nothing
      Sized.AliasDef -> Nothing

deref :: Target -> Lifted.Expr v -> Lifted.Expr v
deref target e
  = Lifted.Case (Lifted.Sized intRep e)
  $ ConBranches
  $ pure
  $ ConBranch
    Ref
    (Telescope $ pure $ TeleArg "dereferenced" () $ Scope unknownSize)
    (toScope $ Lifted.Var $ B 0)
  where
    unknownSize = global "Sixten.Builtin.deref.UnknownSize"
    intRep = Lifted.Lit $ TypeRep $ TypeRep.int target

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
  $ toScope
  $ Lifted.Sized (Lifted.Global "Sixten.Builtin.apply.unknownSize")
  $ Lifted.Case (deref target $ Lifted.Var $ B 0)
  $ ConBranches
  $ pure
  $ ConBranch
    Closure
    (Telescope $ Vector.fromList
      [TeleArg "f_unknown" () $ Scope ptrRep, TeleArg "n" () $ Scope intRep])
    (toScope
      $ Lifted.Case (Lifted.Sized intRep $ Lifted.Var $ B 1)
      $ LitBranches
        [LitBranch (Integer $ fromIntegral arity) $ br arity | arity <- 1 :| [2..maxArity]]
        $ Lifted.Call (global FailName) $ pure $ Lifted.Sized intRep (Lifted.Lit $ TypeRep $ TypeRep.Unit))
  where
    typeRep = Lifted.Lit $ TypeRep $ TypeRep.typeRep target
    intRep = Lifted.Lit $ TypeRep $ TypeRep.int target
    ptrRep = Lifted.Lit $ TypeRep $ TypeRep.ptr target

    directPtr = Direct $ TypeRep.ptr target
    directType = Direct $ TypeRep.typeRep target

    br :: Int -> Lifted.Expr (Var TeleVar (Var TeleVar Void))
    br arity
      | numArgs < arity
        = Lifted.Con Ref
        $ pure
        $ sizedCon (Lifted.Lit $ TypeRep TypeRep.Unit) Closure
        $ Vector.cons (Lifted.Sized ptrRep $ global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Lifted.Sized intRep $ Lifted.Lit $ Integer $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Lifted.Sized ptrRep $ Lifted.Var $ F $ B 0)
        $ (\n -> Lifted.Sized typeRep $ Lifted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> Lifted.Sized (Lifted.Var $ F $ B $ 1 + n) $ Lifted.Var $ F $ B $ 1 + TeleVar numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Lifted.PrimCall (ReturnIndirect OutParam) (Lifted.Var $ B 0)
        $ Vector.cons (directPtr, Lifted.Sized ptrRep $ Lifted.Var $ F $ B 0)
        $ (\n -> (directType, Lifted.Sized typeRep $ Lifted.Var $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Indirect, Lifted.Sized (Lifted.Var $ F $ B $ 1 + n) $ Lifted.Var $ F $ B $ 1 + TeleVar numArgs + n)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Lifted.Call (global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Lifted.Sized ptrRep
          $ Lifted.PrimCall (ReturnIndirect OutParam) (Lifted.Var $ B 0)
          $ Vector.cons (directPtr, Lifted.Sized ptrRep $ Lifted.Var $ F $ B 0)
          $ (\n -> (directType, Lifted.Sized typeRep $ Lifted.Var $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Indirect, Lifted.Sized (Lifted.Var $ F $ B $ 1 + n) $ Lifted.Var $ F $ B $ 1 + fromIntegral numArgs + n)) <$> Vector.enumFromN 0 arity)
        $ (\n -> Lifted.Sized typeRep $ Lifted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> Lifted.Sized (Lifted.Var $ F $ B $ 1 + n) $ Lifted.Var $ F $ B $ 1 + fromIntegral numArgs + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

pap :: Target -> Int -> Int -> Sized.Definition Lifted.Expr Void
pap target k m
  = Sized.FunctionDef Public Sized.NonClosure
  $ Sized.Function
    (Telescope
    $ Vector.cons (TeleArg "this" () $ Scope ptrRep)
    $ (\n -> TeleArg (fromText $ "type" <> shower (unTeleVar n)) () $ Scope typeRep) <$> Vector.enumFromN 0 k
    <|> (\n -> TeleArg (fromText $ "x" <> shower (unTeleVar n)) () $ Scope $ pure $ B $ 1 + n) <$> Vector.enumFromN 0 k)
  $ toScope
  $ Lifted.Sized (Lifted.Global "Sixten.Builtin.pap.unknownSize")
  $ Lifted.Case (deref target $ Lifted.Var $ B 0)
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
      $ Vector.cons (Lifted.Sized ptrRep $ Lifted.Var $ B 2)
      $ (\n -> Lifted.Sized typeRep $ Lifted.Var $ B $ 3 + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Lifted.Sized typeRep $ Lifted.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 k
      <|> (\n -> Lifted.Sized (Lifted.Var $ B $ 3 + n) $ Lifted.Var $ B $ 3 + TeleVar m + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Lifted.Sized (Lifted.Var $ F $ B $ 1 + n) $ Lifted.Var $ F $ B $ 1 + TeleVar k + n) <$> Vector.enumFromN 0 k
    )
  where
    intRep = Lifted.Lit $ TypeRep $ TypeRep.int target
    ptrRep = Lifted.Lit $ TypeRep $ TypeRep.ptr target
    typeRep = Lifted.Lit $ TypeRep $ TypeRep.typeRep target

-- TODO sizes
sizedCon :: Lifted.Expr v -> QConstr -> Vector (Lifted.Expr v) -> Lifted.Expr v
sizedCon tagRep qc args
  = Lifted.Sized (productTypes $ Vector.cons tagRep argTypes) (Lifted.Con qc args)
  where
    argTypes = Lifted.typeOf <$> args

productType :: Lifted.Expr v -> Lifted.Expr v -> Lifted.Expr v
productType a (Lifted.Lit (TypeRep TypeRep.Unit)) = a
productType (Lifted.Lit (TypeRep TypeRep.Unit)) b = b
productType (Lifted.Lit (TypeRep a)) (Lifted.Lit (TypeRep b)) = Lifted.Lit $ TypeRep $ TypeRep.product a b
productType a b = Lifted.Call (global ProductTypeRepName) $ Vector.fromList [a, b]

productTypes :: Vector (Lifted.Expr v) -> Lifted.Expr v
productTypes = foldl' productType (Lifted.Lit (TypeRep TypeRep.Unit))
