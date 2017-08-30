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
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Definition as Sized
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

convertedContext :: Target -> HashMap QName (Sized.Definition Closed.Expr Void)
convertedContext target = HashMap.fromList $ concat
  [[( TypeName
    , constDef $ Closed.Sized typeRep typeRep
    )
  , ( PiTypeName
    , constDef $ Closed.Sized typeRep ptrRep
    )
  , ( PtrName
    , funDef (Telescope $ pure (TeleArg mempty () $ Scope typeRep))
      $ Scope $ Closed.Sized typeRep ptrRep
    )
  , ( IntName
    , constDef $ Closed.Sized typeRep intRep
    )
  , ( ByteName
    , constDef $ Closed.Sized typeRep byteRep
    )
  ]
  , [(papName left given, pap target left given) | given <- [1..maxArity - 1], left <- [1..maxArity - given]]
  , [(applyName arity, apply target arity) | arity <- [1..maxArity]]
  ]
  where
    constDef = Sized.ConstantDef Public . Sized.Constant
    funDef tele = Sized.FunctionDef Public Sized.NonClosure . Sized.Function tele

    intRep = Closed.Lit $ TypeRep $ TypeRep.int target
    typeRep = Closed.Lit $ TypeRep $ TypeRep.typeRep target
    byteRep = Closed.Lit $ TypeRep TypeRep.byte
    ptrRep = Closed.Lit $ TypeRep $ TypeRep.ptr target

convertedSignatures :: Target -> HashMap QName Closed.FunSignature
convertedSignatures target
  = flip HashMap.mapMaybeWithKey (convertedContext target) $ \name def ->
    case def of
      Sized.FunctionDef _ _ (Sized.Function tele s) -> case fromScope s of
        Closed.Anno _ t -> Just (tele, toScope t)
        _ -> error $ "Sixten.Builtin.convertedSignatures " <> show name
      Sized.ConstantDef _ _ -> Nothing
      Sized.AliasDef -> Nothing

deref :: Target -> Closed.Expr v -> Closed.Expr v
deref target e
  = Closed.Case (Closed.Sized intRep e)
  $ ConBranches
  $ pure
  $ ConBranch
    Ref
    (Telescope $ pure $ TeleArg "dereferenced" () $ Scope unknownSize)
    (toScope $ Closed.Var $ B 0)
  where
    unknownSize = global "Sixten.Builtin.deref.UnknownSize"
    intRep = Closed.Lit $ TypeRep $ TypeRep.int target

maxArity :: Num n => n
maxArity = 6

apply :: Target -> Int -> Sized.Definition Closed.Expr Void
apply target numArgs
  = Sized.FunctionDef Public Sized.NonClosure
  $ Sized.Function
    (Telescope
    $ Vector.cons (TeleArg "this" () $ Scope ptrRep)
    $ (\n -> TeleArg (fromText $ "type" <> shower (unTele n)) () $ Scope typeRep) <$> Vector.enumFromN 0 numArgs
    <|> (\n -> TeleArg (fromText $ "x" <> shower (unTele n)) () $ Scope $ pure $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs)
  $ toScope
  $ Closed.Sized (Closed.Global "Sixten.Builtin.apply.unknownSize")
  $ Closed.Case (deref target $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
  $ ConBranch
    Closure
    (Telescope $ Vector.fromList
      [TeleArg "f_unknown" () $ Scope ptrRep, TeleArg "n" () $ Scope intRep])
    (toScope
      $ Closed.Case (Closed.Sized intRep $ Closed.Var $ B 1)
      $ LitBranches
        [LitBranch (Integer $ fromIntegral arity) $ br arity | arity <- 1 :| [2..maxArity]]
        $ Closed.Call (global FailName) $ pure $ Closed.Sized intRep (Closed.Lit $ TypeRep $ TypeRep.Unit))
  where
    typeRep = Closed.Lit $ TypeRep $ TypeRep.typeRep target
    intRep = Closed.Lit $ TypeRep $ TypeRep.int target
    ptrRep = Closed.Lit $ TypeRep $ TypeRep.ptr target

    directPtr = Direct $ TypeRep.ptr target
    directType = Direct $ TypeRep.typeRep target

    br :: Int -> Closed.Expr (Var Tele (Var Tele Void))
    br arity
      | numArgs < arity
        = Closed.Con Ref
        $ pure
        $ sizedCon (Closed.Lit $ TypeRep TypeRep.Unit) Closure
        $ Vector.cons (Closed.Sized ptrRep $ global $ papName (arity - numArgs) numArgs)
        $ Vector.cons (Closed.Sized intRep $ Closed.Lit $ Integer $ fromIntegral $ arity - numArgs)
        $ Vector.cons (Closed.Sized ptrRep $ Closed.Var $ F $ B 0)
        $ (\n -> Closed.Sized typeRep $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n) <$> Vector.enumFromN 0 numArgs
      | numArgs == arity
        = Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
        $ Vector.cons (directPtr, Closed.Sized ptrRep $ Closed.Var $ F $ B 0)
        $ (\n -> (directType, Closed.Sized typeRep $ Closed.Var $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 numArgs
        <|> (\n -> (Indirect, Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele numArgs + n)) <$> Vector.enumFromN 0 numArgs
      | otherwise
        = Closed.Call (global $ applyName $ numArgs - arity)
        $ Vector.cons
          (Closed.Sized ptrRep
          $ Closed.PrimCall (ReturnIndirect OutParam) (Closed.Var $ B 0)
          $ Vector.cons (directPtr, Closed.Sized ptrRep $ Closed.Var $ F $ B 0)
          $ (\n -> (directType, Closed.Sized typeRep $ Closed.Var $ F $ B $ 1 + n)) <$> Vector.enumFromN 0 arity
          <|> (\n -> (Indirect, Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n)) <$> Vector.enumFromN 0 arity)
        $ (\n -> Closed.Sized typeRep $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)
        <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + fromIntegral numArgs + n) <$> Vector.enumFromN (fromIntegral arity) (numArgs - arity)

pap :: Target -> Int -> Int -> Sized.Definition Closed.Expr Void
pap target k m
  = Sized.FunctionDef Public Sized.NonClosure
  $ Sized.Function
    (Telescope
    $ Vector.cons (TeleArg "this" () $ Scope ptrRep)
    $ (\n -> TeleArg (fromText $ "type" <> shower (unTele n)) () $ Scope typeRep) <$> Vector.enumFromN 0 k
    <|> (\n -> TeleArg (fromText $ "x" <> shower (unTele n)) () $ Scope $ pure $ B $ 1 + n) <$> Vector.enumFromN 0 k)
  $ toScope
  $ Closed.Sized (Closed.Global "Sixten.Builtin.pap.unknownSize")
  $ Closed.Case (deref target $ Closed.Var $ B 0)
  $ ConBranches
  $ pure
  $ ConBranch
    Closure
    (Telescope
      $ Vector.cons (TeleArg "_" () $ Scope ptrRep)
      $ Vector.cons (TeleArg "_" () $ Scope intRep)
      $ Vector.cons (TeleArg "that" () $ Scope ptrRep)
      $ (\n -> TeleArg (fromText $ "type" <> shower (unTele n)) () $ Scope typeRep) <$> Vector.enumFromN 0 m
      <|> (\n -> TeleArg (fromText $ "y" <> shower (unTele n)) () $ Scope $ pure $ B $ 3 + n) <$> Vector.enumFromN 0 m)
    (toScope
      $ Closed.Call (global $ applyName $ m + k)
      $ Vector.cons (Closed.Sized ptrRep $ Closed.Var $ B 2)
      $ (\n -> Closed.Sized typeRep $ Closed.Var $ B $ 3 + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Closed.Sized typeRep $ Closed.Var $ F $ B $ 1 + n) <$> Vector.enumFromN 0 k
      <|> (\n -> Closed.Sized (Closed.Var $ B $ 3 + n) $ Closed.Var $ B $ 3 + Tele m + n) <$> Vector.enumFromN 0 m
      <|> (\n -> Closed.Sized (Closed.Var $ F $ B $ 1 + n) $ Closed.Var $ F $ B $ 1 + Tele k + n) <$> Vector.enumFromN 0 k
    )
  where
    intRep = Closed.Lit $ TypeRep $ TypeRep.int target
    ptrRep = Closed.Lit $ TypeRep $ TypeRep.ptr target
    typeRep = Closed.Lit $ TypeRep $ TypeRep.typeRep target

-- TODO sizes
sizedCon :: Closed.Expr v -> QConstr -> Vector (Closed.Expr v) -> Closed.Expr v
sizedCon tagRep qc args
  = Closed.Sized (productTypes $ Vector.cons tagRep argTypes) (Closed.Con qc args)
  where
    argTypes = Closed.typeOf <$> args

productType :: Closed.Expr v -> Closed.Expr v -> Closed.Expr v
productType a (Closed.Lit (TypeRep TypeRep.Unit)) = a
productType (Closed.Lit (TypeRep TypeRep.Unit)) b = b
productType (Closed.Lit (TypeRep a)) (Closed.Lit (TypeRep b)) = Closed.Lit $ TypeRep $ TypeRep.product a b
productType a b = Closed.Call (global ProductTypeRepName) $ Vector.fromList [a, b]

productTypes :: Vector (Closed.Expr v) -> Closed.Expr v
productTypes = foldl' productType (Closed.Lit (TypeRep TypeRep.Unit))
