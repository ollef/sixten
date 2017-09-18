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
typeOfM = typeOfGen abstract1M

typeOf
  :: AbstractM
  -> VIX AbstractM
typeOf = typeOfGen (\x e -> pure $ abstract1 x e)

typeOfGen
  :: (MetaA -> AbstractM -> VIX (Scope () Expr MetaA))
  -> AbstractM
  -> VIX AbstractM
typeOfGen abstr expr = do
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
      resType  <- typeOfGen abstr (instantiate1 (pure x) s)
      abstractedResType <- abstr x resType
      return $ Pi h a t abstractedResType
    App e1 a e2 -> do
      e1type <- typeOfGen abstr e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ a' _ resType | a == a' -> return $ instantiate1 e2 resType
        _ -> throwError $ "typeOfGen: expected pi type " ++ show e1type'
    Let ds s -> do
      xs <- forMLet ds $ \h _ t -> forall h t
      typeOfGen abstr $ instantiateLet pure xs s
    Case _ _ retType -> return retType
    ExternCode _ retType -> return retType
  modifyIndent pred
  return t

typeOfLiteral
  :: Literal
  -> Expr v
typeOfLiteral Integer {} = Builtin.IntType
typeOfLiteral Byte {} = Builtin.ByteType
typeOfLiteral TypeRep {} = Builtin.Type
