{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.Constructor where

import Control.Monad.Except
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.Monoid
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Inference.Constraint
import Inference.Meta
import Inference.Monad
import Syntax
import qualified Syntax.Abstract as Abstract
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
      ["There is no data type with the" Leijen.<+> constrDoc <> "."]

  let candidates
        = maybe
          cs
          (\e -> HashSet.filter ((== e) . qconstrTypeName) cs)
          mExpectedTypeName

  case (HashSet.toList candidates, mExpectedTypeName) of
    ([], Just expectedTypeName) ->
      err "Undefined constructor"
        [ Leijen.dullgreen (pretty expectedTypeName)
        Leijen.<+> "doesn't define the constructor"
        Leijen.<+> constrDoc <> "."
        ]
    ([x], _) -> return x
    (xs, _) -> err "Ambiguous constructor"
      [ "Unable to determine which constructor" Leijen.<+> constrDoc Leijen.<+> "refers to."
      , "Possible candidates:"
      Leijen.<+> prettyHumanList "and" (Leijen.dullgreen . pretty <$> xs)
      <> "."
      ]
  where
    expectedDataType = join <$> traverse findExpectedDataType expected
    findExpectedDataType :: AbstractM -> Infer (Maybe QName)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h p t s -> do
          v <- forall h p t
          findExpectedDataType $ Util.instantiate1 (pure v) s
        Abstract.App t1 _ _ -> findExpectedDataType t1
        Abstract.Global v -> do
          (d, _) <- definition v
          return $ case d of
            DataDefinition _ _ -> Just v
            _ -> Nothing
        _ -> return Nothing
    err heading docs = do
      loc <- currentLocation
      throwError
        $ show
        $ explain loc
        $ Err (Just heading) docs mempty mempty
    constrDoc = case HashSet.toList cs of
      (QConstr _ cname:_) -> Leijen.red (pretty cname)
      _ -> error "resolveConstr no constrs"

