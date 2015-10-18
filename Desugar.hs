{-# LANGUAGE OverloadedStrings #-}
-- | Desugaring of programs
module Desugar where

import Bound
import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.Map(Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text

import Data
import Input
import Util

program :: (Ord v, Show v) => [TopLevelParsed v] -> Either Text (Program v)
program xs = snd <$> foldlM resolveName (Nothing, mempty) xs >>= matchTypes
  where
    resolveName :: (Ord v, Show v)
                => (Maybe v, (Map v (Expr v), Map v (Type v), Map v (DataDef Type v)))
                -> TopLevelParsed v
                -> Either Text (Maybe v, (Map v (Expr v), Map v (Type v), Map v (DataDef Type v)))
    resolveName (prevName, (defs, types, datas)) (ParsedDefLine mn e) = case mn <|> prevName of
      Nothing -> throwError "not sure what a wildcard definition refers to"
      Just n  -> do
        defs' <- insertNoDup (throwError $ "duplicate definition: " <> shower n) n e defs
        return (Just n, (defs', types, datas))
    resolveName (_, (defs, types, datas)) (ParsedTypeDecl n e) = do
      types' <- insertNoDup (throwError $ "duplicate type declaration: " <> shower n) n e types
      return (Just n, (defs, types', datas))
    resolveName (_, (defs, types, datas)) (ParsedData n dataDef) = do
      datas' <- insertNoDup (throwError $ "duplicate datatype: " <> shower n) n dataDef datas
      return (Just n, (defs, types, datas'))
    insertNoDup err k v m = case M.insertLookupWithKey (\_ new _ -> new) k v m of
      (Just _, _)   -> err
      (Nothing, m') -> return m'
    matchTypes :: (Ord v, Show v)
               => (Map v (Expr v), Map v (Type v), Map v (DataDef Type v))
               -> Either Text (Program v)
    matchTypes (defs, types, datas) = case M.keys $ M.difference types defs of
      [] -> do
        let defs' = M.unionWith (\(e, _) (t, _) -> (e, t)) (flip (,) Wildcard <$> defs)
                                                           (flip (,) Wildcard <$> types)
            ldefs = first Definition <$> defs'
            rdatas = (\x -> (DataDefinition x, dataType x Pi (Scope Type))) <$> datas
        case M.keys $ M.intersection ldefs rdatas of
          [] -> return $ ldefs <> rdatas
          vs -> throwError $ "duplicate definition: " <> Text.intercalate ", " (map shower vs)
      vs -> throwError $ "type without a definition: " <> Text.intercalate ", " (map shower vs)
