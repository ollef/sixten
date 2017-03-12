{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module Inference.TypeOf where

import Control.Monad.Except
import qualified Data.List.NonEmpty as NonEmpty

import qualified Builtin
import Inference.Normalise
import Meta
import Syntax
import Syntax.Abstract
import VIX

typeOfM
  :: AbstractM
  -> VIX AbstractM
typeOfM expr = do
  -- logMeta "typeOfM" expr
  modifyIndent succ
  t <- case expr of
    Global v -> do
      (_, typ) <- definition v
      return typ
    Var v -> return $ metaType v
    Con qc -> qconstructor qc
    Lit _ -> return Builtin.IntType
    Pi {} -> return Builtin.Type
    Lam h a t s -> do
      x <- forall h t
      resType  <- typeOfM (instantiate1 (pure x) s)
      abstractedResType <- abstract1M x resType
      return $ Pi h a t abstractedResType
    App e1 a e2 -> do
      e1type <- typeOfM e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ a' _ resType | a == a' -> return $ instantiate1 e2 resType
        _ -> throwError $ "typeOfM: expected pi type " ++ show e1type'
    Let h e s -> do
      eType <- typeOfM e
      v <- forall h eType
      typeOfM $ instantiate1 (pure v) s
    Case _ (ConBranches ((_, tele, brScope) NonEmpty.:| _)) -> do
      vs <- forTeleWithPrefixM tele $ \h _ s vs ->
        forall h $ instantiateTele pure vs s
      typeOfM $ instantiateTele pure vs brScope
    Case _ (LitBranches _ def) -> typeOfM def
    Case _ (NoBranches t) -> return t
  modifyIndent pred
  -- logMeta "typeOfM res" =<< zonk t
  return t

typeOf
  :: AbstractM
  -> VIX AbstractM
typeOf expr = do
  -- logMeta "typeOf" expr
  modifyIndent succ
  t <- case expr of
    Global v -> do
      (_, typ) <- definition v
      return typ
    Var v -> return $ metaType v
    Con qc -> qconstructor qc
    Lit _ -> return Builtin.IntType
    Pi {} -> return Builtin.Type
    Lam h a t s -> do
      x <- forall h t
      resType <- typeOf (instantiate1 (pure x) s)
      let abstractedResType = abstract1 x resType
      return $ Pi h a t abstractedResType
    App e1 a e2 -> do
      e1type <- typeOf e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ a' _ resType | a == a' -> return $ instantiate1 e2 resType
        _ -> throwError $ "typeOf: expected pi type " ++ show e1type'
    Let h e s -> do
      eType <- typeOf e
      v <- forall h eType
      typeOf $ instantiate1 (pure v) s
    Case _ (ConBranches ((_, tele, brScope) NonEmpty.:| _)) -> do
      vs <- forTeleWithPrefixM tele $ \h _ s vs ->
        forall h $ instantiateTele pure vs s
      typeOf $ instantiateTele pure vs brScope
    Case _ (LitBranches _ def) -> typeOf def
    Case _ (NoBranches t) -> return t
  modifyIndent pred
  -- logMeta "typeOf res" =<< zonk t
  return t
