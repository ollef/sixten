{-# LANGUAGE FlexibleContexts, OverloadedStrings, TypeFamilies #-}
module Inference.TypeOf where

import Control.Monad.Except
import qualified Data.Text.Prettyprint.Doc as PP

import qualified Builtin.Names as Builtin
import Inference.Meta
import Inference.Normalise
import Syntax
import Syntax.Abstract
import Util
import VIX

typeOfM
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => AbstractM
  -> m AbstractM
typeOfM = typeOfGen abstract1M

typeOf
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => AbstractM
  -> m AbstractM
typeOf = typeOfGen (\x e -> pure $ abstract1 x e)

typeOfGen
  :: (MonadIO m, MonadVIX m, MonadError Error m, MonadFix m)
  => (MetaA -> AbstractM -> m (Scope () Expr MetaA))
  -> AbstractM
  -> m AbstractM
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
    Lam h p t s -> do
      x <- forall h p t
      resType  <- typeOfGen abstr (instantiate1 (pure x) s)
      abstractedResType <- abstr x resType
      return $ Pi h p t abstractedResType
    App e1 p e2 -> do
      e1type <- typeOfGen abstr e1
      e1type' <- whnf e1type
      case e1type' of
        Pi _ p' _ resType | p == p' -> return $ instantiate1 e2 resType
        _ -> internalError $ "typeOfGen: expected" PP.<+> shower p PP.<+> "pi type" PP.<+> shower e1type'
    Let ds s -> do
      xs <- forMLet ds $ \h _ t -> forall h Explicit t
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
