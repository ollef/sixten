{-# LANGUAGE FlexibleContexts #-}
module Context where

import Control.Monad.Except
import Data.Bifunctor
import Data.Set(Set)
import qualified Data.Set as Set

import Syntax
import Syntax.Abstract
import Util

class Monad cxt => Context cxt where
  lookupDefinition :: Name -> cxt (Maybe (Definition Expr v, Type v))
  lookupConstructor :: Ord v => Constr -> cxt (Set (Name, Type v))

definition
  :: (MonadError String cxt, Context cxt)
  => Name
  -> cxt (Definition Expr v, Type v)
definition v = do
  mres <- lookupDefinition v
  maybe (throwError $ "Not in scope: " ++ show v)
        (return . bimap (fmap fromEmpty) (fmap fromEmpty))
        mres

constructor
  :: (MonadError String cxt, Context cxt, Ord v)
  => Either Constr QConstr
  -> cxt (Set (Name, Type v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c) = Set.map (second $ fmap fromEmpty) <$> lookupConstructor c

qconstructor
  :: (MonadError String cxt, Context cxt)
  => QConstr
  -> cxt (Type v)
qconstructor qc@(QConstr n c) = do
  results <- lookupConstructor c
  let filtered = Set.filter ((== n) . fst) results
  case Set.size filtered of
    1 -> do
      let [(_, t)] = Set.toList filtered
      return (fromEmpty <$> t)
    0 -> throwError $ "Not in scope: constructor " ++ show qc
    _ -> throwError $ "Ambiguous constructor: " ++ show qc
