{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module Inference.TypeOf where

import Control.Monad.Except

import qualified Builtin.Names as Builtin
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
    Lit l -> return $ typeOfLiteral l
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
    Case _ _ retType -> return retType
    ExternCode _ retType -> return retType
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
    Lit l -> return $ typeOfLiteral l
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
    Case _ _ retType -> return retType
    ExternCode _ retType -> return retType
  modifyIndent pred
  -- logMeta "typeOf res" =<< zonk t
  return t

typeOfLiteral
  :: Literal
  -> Expr v
typeOfLiteral Integer {} = Builtin.IntType
typeOfLiteral Byte {} = Builtin.ByteType
typeOfLiteral TypeRep {} = Builtin.Type
