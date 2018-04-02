{-# LANGUAGE FlexibleContexts #-}
module Inference.MetaVar.Zonk where

import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Const
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import Syntax
import Syntax.Abstract

zonk :: MonadIO m => Expr MetaVar v -> m (Expr MetaVar v)
zonk = hoistMetas $ \m es -> do
  sol <- solution m
  case sol of
    Left _ -> return $ Meta m es
    Right e -> return $ betaApps (vacuous e) es

zonkDef :: MonadIO m => Definition (Expr MetaVar) v -> m (Definition (Expr MetaVar) v)
zonkDef = transverseDefinition zonk

metaVars :: MonadIO m => Expr MetaVar v -> m (HashSet MetaVar)
metaVars expr = execStateT (hoistMetas_ go expr) mempty
  where
    go m = do
      visited <- get
      unless (m `HashSet.member` visited) $ do
        put $ HashSet.insert m visited
        sol <- solution m
        case sol of
          Left _ -> hoistMetas_ go $ metaType m
          Right e -> hoistMetas_ go e

definitionMetaVars
  :: MonadIO m
  => Definition (Expr MetaVar) v
  -> m (HashSet MetaVar)
definitionMetaVars def = do
  x <- transverseDefinition (fmap Const . metaVars) def
  return $ getConst $ bitraverseDefinition Const (const $ Const mempty) x
