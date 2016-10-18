{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module TypeOf where

import Control.Monad
import Control.Monad.Except

import Meta
import Syntax
import Syntax.Abstract
import TCM
import qualified Builtin
import Normalise

typeOfM
  :: AbstractM
  -> TCM AbstractM
typeOfM expr = do
  -- tr "typeOfM" expr
  modifyIndent succ
  t <- case expr of
    Global v -> do
      (_, typ) <- definition v
      return typ
    Var v -> return $ metaType v
    Con qc -> qconstructor qc
    Lit _ -> return Builtin.Size
    Pi {} -> return $ Builtin.TypeP $ Lit 1
    Lam n a t s -> do
      x <- forall n a t
      resType  <- typeOfM (instantiate1 (pure x) s)
      abstractedResType <- abstract1M x resType
      return $ Pi n a t abstractedResType
    App e1 a e2 -> do
      e1type <- typeOfM e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ a' _ resType | a == a' -> return $ instantiate1 e2 resType
        _ -> throwError $ "typeOfM: expected pi type " ++ show e1type'
    Case _ (ConBranches _ t) -> return t -- TODO do this properly to get rid of the ConBranches type field
    Case _ (LitBranches _ def) -> typeOfM def
  modifyIndent pred
  -- tr "typeOfM res" =<< zonk t
  return t

typeOf
  :: (MetaData (Expr a) v ~ a, Context (Expr a), Eq a, Show a, Show v, MetaVary (Expr a) v)
  => Expr a v
  -> TCM (Expr a v)
typeOf expr = do
  -- tr "typeOf" expr
  modifyIndent succ
  t <- case expr of
    Global v -> do
      (_, typ) <- definition v
      return typ
    Var v -> return $ metaVarType v
    Con qc -> qconstructor qc
    Lit _ -> return Builtin.Size
    Pi {} -> return $ typeOfSize 1
    Lam n a t s -> do
      x <- forall n a t
      resType <- typeOf (instantiate1 (pure x) s)
      let abstractedResType = abstract1 x resType
      return $ Pi n a t abstractedResType
    App e1 a e2 -> do
      e1type <- typeOf e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ a' _ resType | a == a' -> return $ instantiate1 e2 resType
        _ -> throwError $ "typeOf: expected pi type " ++ show e1type'
    Case _ (ConBranches _ t) -> return t -- TODO do this properly to get rid of the ConBranches type field
    Case _ (LitBranches _ def) -> typeOf def
  modifyIndent pred
  -- tr "typeOf res" =<< zonk t
  return t

sizeOfType
  :: (MetaData (Expr a) v ~ a, Context (Expr a), Eq a, Show a, Show v, MetaVary (Expr a) v)
  => Expr a v
  -> TCM (Expr a v)
sizeOfType expr = do
  -- tr "sizeOf" expr
  modifyIndent succ
  t <- whnf =<< typeOf expr
  case t of
    Builtin.Type _ sz -> do
      modifyIndent pred
      -- tr "sizeOf res" sz
      return sz
    _ -> throwError $ "sizeOfType: Not a type: " ++ show t

sizeOf
  :: (MetaData (Expr a) v ~ a, Context (Expr a), Eq a, Show a, Show v, MetaVary (Expr a) v)
  => Expr a v
  -> TCM (Expr a v)
sizeOf = typeOf >=> sizeOfType
