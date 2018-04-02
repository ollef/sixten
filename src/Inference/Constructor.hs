{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.Constructor where

import Control.Monad.Except
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP

import Inference.Constraint
import Inference.Monad
import Syntax
import qualified Syntax.Abstract as Abstract
import TypedFreeVar
import Util
import VIX

resolveConstr
  :: HashSet QConstr
  -> Maybe Rhotype
  -> Infer QConstr
resolveConstr cs expected = do
  mExpectedTypeName <- expectedDataType

  when (HashSet.null cs) $
    err
      "No such data type"
      ["There is no data type with the" PP.<+> constrDoc <> "."]

  let candidates
        = maybe
          cs
          (\e -> HashSet.filter ((== e) . qconstrTypeName) cs)
          mExpectedTypeName

  case (HashSet.toList candidates, mExpectedTypeName) of
    ([], Just expectedTypeName) ->
      err "Undefined constructor"
        [ dullGreen (pretty expectedTypeName)
        PP.<+> "doesn't define the constructor"
        PP.<+> constrDoc <> "."
        ]
    ([x], _) -> return x
    (xs, _) -> err "Ambiguous constructor"
      [ "Unable to determine which constructor" PP.<+> constrDoc PP.<+> "refers to."
      , "Possible candidates:"
      PP.<+> prettyHumanList "and" (dullGreen . pretty <$> xs)
      <> "."
      ]
  where
    expectedDataType = join <$> traverse findExpectedDataType expected
    findExpectedDataType :: AbstractM -> Infer (Maybe QName)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h p t s -> do
          v <- freeVar h p t
          findExpectedDataType $ Util.instantiate1 (pure v) s
        Abstract.App t1 _ _ -> findExpectedDataType t1
        Abstract.Global v -> do
          (d, _) <- definition v
          return $ case d of
            DataDefinition _ _ -> Just v
            _ -> Nothing
        _ -> return Nothing
    err heading docs = throwLocated $ heading <> PP.line <> PP.vcat docs
    constrDoc = case HashSet.toList cs of
      (QConstr _ cname:_) -> red (pretty cname)
      _ -> error "resolveConstr no constrs"

