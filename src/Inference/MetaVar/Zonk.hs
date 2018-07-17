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
import Syntax.Core

zonk :: MonadIO m => Expr MetaVar v -> m (Expr MetaVar v)
zonk = hoistMetas $ \m es -> do
  msol <- solution m
  case msol of
    Nothing -> return $ Meta m es
    Just e -> do
      e' <- zonk e
      solve m e'
      return $ betaApps (vacuous e') es

metaVars :: MonadIO m => Expr MetaVar v -> m (HashSet MetaVar)
metaVars expr = execStateT (hoistMetas_ go expr) mempty
  where
    go m = do
      visited <- get
      unless (m `HashSet.member` visited) $ do
        put $ HashSet.insert m visited
        msol <- solution m
        case msol of
          Nothing -> hoistMetas_ go $ metaType m
          Just e -> hoistMetas_ go e

definitionMetaVars
  :: MonadIO m
  => Definition (Expr MetaVar) v
  -> m (HashSet MetaVar)
definitionMetaVars def = do
  x <- transverseDefinition (fmap Const . metaVars) def
  return $ getConst $ bitraverseDefinition Const (const $ Const mempty) x
