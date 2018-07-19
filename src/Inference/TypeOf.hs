{-# LANGUAGE ConstraintKinds, FlexibleContexts, OverloadedStrings, TypeFamilies #-}
module Inference.TypeOf where

import Control.Monad.Except
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Void

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import Inference.Monad
import qualified Inference.Normalise as Normalise
import MonadContext
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import VIX

type ExprFreeVar meta = FreeVar Plicitness (Expr meta)

type MonadTypeOf meta m = (Show meta, MonadIO m, MonadVIX m, MonadError Error m, MonadContext (ExprFreeVar meta) m, MonadFix m)

data Args meta m = Args
  { typeOfMeta :: !(meta -> Closed (Expr meta))
  , normaliseArgs :: !(Normalise.Args meta m)
  }

metaVarArgs :: MonadIO m => Args MetaVar m
metaVarArgs = Args metaType Normalise.metaVarSolutionArgs

voidArgs :: Args Void m
voidArgs = Args absurd Normalise.voidArgs

typeOf :: MonadTypeOf MetaVar m => CoreM -> m CoreM
typeOf = typeOf' metaVarArgs

typeOf'
  :: MonadTypeOf meta m
  => Args meta m
  -> Expr meta (ExprFreeVar meta)
  -> m (Expr meta (ExprFreeVar meta))
typeOf' args expr = case expr of
  Global v -> do
    (_, typ) <- definition v
    return typ
  Var v -> return $ varType v
  Meta m es -> case typeApps (open $ typeOfMeta args m) es of
    Nothing -> error "typeOf meta typeApps"
    Just t -> return t
  Con qc -> qconstructor qc
  Lit l -> return $ typeOfLiteral l
  Pi {} -> return Builtin.Type
  Lam h p t s -> do
    x <- forall h p t
    resType <- withVar x $ typeOf' args $ instantiate1 (pure x) s
    return $ pi_ x resType
  App e1 p e2 -> do
    e1type <- typeOf' args e1
    e1type' <- Normalise.whnf' (normaliseArgs args) e1type mempty
    case e1type' of
      Pi _ p' _ resType | p == p' -> return $ instantiate1 e2 resType
      _ -> internalError $ "typeOf: expected" PP.<+> shower p PP.<+> "pi type"
        <> PP.line <> "actual type: " PP.<+> shower e1type'
  Let ds s -> do
    xs <- forMLet ds $ \h _ t -> forall h Explicit t
    withVars xs $ typeOf' args $ instantiateLet pure xs s
  Case _ _ retType -> return retType
  ExternCode _ retType -> return retType

typeOfLiteral
  :: Literal
  -> Expr meta v
typeOfLiteral Integer {} = Builtin.IntType
typeOfLiteral Byte {} = Builtin.ByteType
typeOfLiteral TypeRep {} = Builtin.Type
