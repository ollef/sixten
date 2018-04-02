{-# LANGUAGE ConstraintKinds, FlexibleContexts, OverloadedStrings, TypeFamilies #-}
module Inference.TypeOf where

import Control.Monad.Except
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Void

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import Inference.Monad
import Inference.Normalise
import MonadContext
import Syntax
import Syntax.Abstract
import TypedFreeVar
import Util
import VIX

type MonadTypeOf m = (MonadIO m, MonadVIX m, MonadError Error m, MonadContext FreeV m, MonadFix m)

typeOf
  :: MonadTypeOf m
  => AbstractM
  -> m AbstractM
typeOf expr = case expr of
  Global v -> do
    (_, typ) <- definition v
    return typ
  Var v -> return $ varType v
  Meta m es -> case typeApps (vacuous $ metaType m) es of
    Nothing -> error "typeOf meta typeApps"
    Just t -> return t
  Con qc -> qconstructor qc
  Lit l -> return $ typeOfLiteral l
  Pi {} -> return Builtin.Type
  Lam h p t s -> do
    x <- forall h p t
    resType  <- withVar x $ typeOf $ instantiate1 (pure x) s
    let abstractedResType = abstract1 x resType
    return $ Pi h p t abstractedResType
  App e1 p e2 -> do
    e1type <- typeOf e1
    e1type' <- whnf e1type
    case e1type' of
      Pi _ p' _ resType | p == p' -> return $ instantiate1 e2 resType
      _ -> internalError $ "typeOf: expected" PP.<+> shower p PP.<+> "pi type"
        <> PP.line <> "actual type: " PP.<+> shower e1type'
  Let ds s -> do
    xs <- forMLet ds $ \h _ t -> forall h Explicit t
    withVars xs $ typeOf $ instantiateLet pure xs s
  Case _ _ retType -> return retType
  ExternCode _ retType -> return retType

typeOfLiteral
  :: Literal
  -> Expr meta v
typeOfLiteral Integer {} = Builtin.IntType
typeOfLiteral Byte {} = Builtin.ByteType
typeOfLiteral TypeRep {} = Builtin.Type
