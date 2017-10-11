{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
module Inference.Monad where

import Control.Monad.Reader

import qualified Builtin.Names as Builtin
import Meta
import Syntax
import Syntax.Abstract
import VIX

type Polytype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

newtype InstUntil = InstUntil Plicitness
  deriving (Eq, Ord, Show)

shouldInst :: Plicitness -> InstUntil -> Bool
shouldInst Explicit _ = False
shouldInst _ (InstUntil Explicit) = True
shouldInst p (InstUntil p') | p == p' = False
shouldInst _ _ = True

type Witness = AbstractM

-- TODO move level and location from VIX to this
newtype InferEnv = InferEnv
  { constraints :: [(Witness, AbstractM)]
  }

type Infer = ReaderT InferEnv VIX

runInfer :: Infer a -> VIX a
runInfer i = runReaderT i InferEnv { constraints = mempty }

existsType
  :: (MonadVIX m, MonadIO m)
  => Applicative e
  => NameHint
  -> m (e MetaA)
existsType n = pure <$> exists n Explicit Builtin.Type

pattern UnsolvedConstraint :: Expr v -> Expr v
pattern UnsolvedConstraint typ = App (Global Builtin.UnsolvedConstraintName) Explicit typ

existsVar
  :: (MonadVIX m, MonadIO m)
  => NameHint
  -> Plicitness
  -> AbstractM
  -> m AbstractM
existsVar _ Constraint typ = return $ UnsolvedConstraint typ
existsVar h Implicit typ = pure <$> exists h Implicit typ
existsVar h Explicit typ = pure <$> exists h Explicit typ
