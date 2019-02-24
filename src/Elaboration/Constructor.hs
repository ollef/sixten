{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.Constructor where

import Protolude

import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Elaboration.Constraint
import Elaboration.Monad
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import Util
import qualified Util.Tsil as Tsil

resolveConstr
  :: HashSet QConstr
  -> Maybe Rhotype
  -> Elaborate QConstr
resolveConstr cs expected = do
  mExpectedTypeName <- expectedDataType

  let candidates
        = maybe
          cs
          (\e -> HashSet.filter ((== e) . qconstrTypeName) cs)
          mExpectedTypeName

  case (HashSet.toList candidates, mExpectedTypeName) of
    ([], Just expectedTypeName) ->
      err cs "Undefined constructor"
        [ dullGreen (pretty expectedTypeName)
        PP.<+> "doesn't define the constructor"
        PP.<+> constrDoc <> "."
        ]
    ([x], _) -> return x
    (xs, _) -> err candidates "Ambiguous constructor"
      [ "Unable to determine which constructor" PP.<+> constrDoc PP.<+> "refers to."
      , "Possible candidates:"
      PP.<+> prettyHumanList "and" (dullGreen . pretty <$> xs)
      <> "."
      ]
  where
    expectedDataType = join <$> traverse findExpectedDataType expected
    findExpectedDataType :: CoreM -> Elaborate (Maybe QName)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Core.Pi h p t s ->
          Context.freshExtend (binding h p t) $ \v ->
            findExpectedDataType $ Util.instantiate1 (pure v) s
        Core.App t1 _ _ -> findExpectedDataType t1
        Builtin.QGlobal v -> do
          d <- fetchDefinition $ gname v
          return $ case d of
            DataDefinition _ _ -> Just v
            _ -> Nothing
        _ -> return Nothing
    err candidates heading docs = do
      reportLocated $ heading <> PP.line <> PP.vcat docs
      -- Assume it's the first candidate to be able to keep going
      return $ case HashSet.toList candidates of
        qc:_ -> qc
        _ -> panic "resolveConstr: empty constr list"
    constrDoc = case HashSet.toList cs of
      QConstr _ cname:_ -> red (pretty cname)
      _ -> panic "resolveConstr no constrs"

constrainConstructorIndices
  :: CoreM
  -> Elaborate ()
constrainConstructorIndices = go mempty
  where
    go vs constrType_ = do
      constrType' <- whnf constrType_
      case constrType' of
        Core.Pi h p t s ->
          Context.freshExtend (binding h p t) $ \v ->
            go (Tsil.Snoc vs v) $ instantiate1 (pure v) s
        (Core.appsView -> (_, toVector -> args)) -> do
          let
            varVec = toVector vs
          unless (Vector.length varVec >= Vector.length args) $
            panic "constrainConstructorIndices too few vars"
          Vector.zipWithM_
            (\v (_, arg) -> runUnify (unify [] (pure v) arg) report)
            varVec
            args
