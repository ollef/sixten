-- | Desugaring of programs
module Desugar where

import Control.Applicative
import Control.Monad.Except
import Data.Foldable
import Data.List
import Data.Map(Map)
import qualified Data.Map as M

import Input

program :: (Ord v, Show v) => [TopLevel v] -> Either String (Program v)
program xs = snd <$> foldlM resolveName (Nothing, mempty) xs >>= matchTypes
  where
    resolveName :: (Ord v, Show v)
                => (Maybe v, (Map v (Expr v), Map v (Type v)))
                -> TopLevel v
                -> Either String (Maybe v, (Map v (Expr v), Map v (Type v)))
    resolveName (prevName, (defs, types)) (DefLine mn e) = case mn <|> prevName of
      Nothing -> throwError "not sure what a wildcard definition refers to"
      Just n  -> do
        defs' <- insertNoDup (throwError $ "duplicate definition: " ++ show n) n e defs
        return (Just n, (defs', types))
    resolveName (_, (defs, types)) (TypeDecl n e) = do
      types' <- insertNoDup (throwError $ "duplicate type declaration: " ++ show n) n e types
      return (Just n, (defs, types'))
    insertNoDup err k v m = case M.insertLookupWithKey (\_ new _ -> new) k v m of
      (Just _, _)   -> err
      (Nothing, m') -> return m'
    matchTypes :: (Ord v, Show v)
               => (Map v (Expr v), Map v (Type v))
               -> Either String (Program v)
    matchTypes (defs, types) = case M.keys $ M.difference types defs of
      [] -> return $ M.unionWith (\(e, _) (t, _) -> (e, t)) (flip (,) Wildcard <$> defs)
                                                            (flip (,) Wildcard <$> types)
      vs -> throwError $ "type without a definition: " ++ intercalate ", " (map show vs)


{-
program :: (Ord v, Show v) => [TopLevel v] -> Either String (Program v)
program xs = evalStateT (foldrM resolveName mempty xs) Nothing >>= matchTypes
  where
    resolveName :: (Ord v, Show v)
                => TopLevel v
                -> (Map v (Expr v), Map v (Type v))
                -> StateT (Maybe v) (Either String) (Map v (Expr v), Map v (Type v))
    resolveName (DefLine mn e) (defs, types) = do
      prevName <- get
      case mn <|> prevName of
        Nothing -> throwError "not sure what a wildcard definition refers to"
        Just n  -> do
          defs' <- insertNoDup (throwError $ "duplicate definition: " ++ show n) n e defs
          put $ Just n
          return (defs', types)
    resolveName (TypeDecl n e) (defs, types) = do
      types' <- insertNoDup (throwError $ "duplicate type declaration: " ++ show n) n e types
      put $ Just n
      return (defs, types')
    insertNoDup err k v m = case M.insertLookupWithKey (\_ new _ -> new) k v m of
      (Just _, _)   -> err
      (Nothing, m') -> return m'
    matchTypes :: (Ord v, Show v)
               => (Map v (Expr v), Map v (Type v))
               -> Either String (Program v)
    matchTypes (defs, types) = case M.keys $ M.difference types defs of
      [] -> return $ M.unionWith (\(e, _) (t, _) -> (e, t)) (flip (,) Wildcard <$> defs)
                                                            (flip (,) Wildcard <$> types)
      vs -> throwError $ "type without a definition: " ++ intercalate ", " (map show vs)
      -}
