{-# LANGUAGE OverloadedStrings #-}
module Erasure where

import Bound.Scope
import Data.Maybe
import Data.Text
import Data.HashMap.Strict(HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Lambda as Lambda

type Abstract = Abstract.Expr
type Lambda = Lambda.Expr

data Relevance = Irrelevant | Relevant (Vector Relevance)

relevance :: HashMap (MetaVar s) Relevance -> AbstractM s -> TCM s Relevance
relevance r expr = case expr of
  Abstract.Var v -> return $ r HashMap.! v
  Abstract.Global g -> _ $ context g
  Abstract.Con c -> return Irrelevant
  Abstract.Lit l -> return Irrelevant
  Abstract.Pi h _ t s -> do
    r <- relevance r t
    forall_ h t s
    instantiate1 
  Abstract.Lam h _ t s -> do
    Lambda.etaLam h (erase t) $ toScope $ erase $ fromScope s
  Abstract.App e1 a e2 -> Lambda.App (erase e1) (erase e2)
  Abstract.Case e brs -> Lambda.Case (erase e) (eraseBranches brs)

erase
  :: HashMap (MetaVar s) Relevance
  -> AbstractM s
  -> TCM s (LambdaM v)
erase r expr = case expr of
  Abstract.Var v -> return $ Lambda.Var v
  Abstract.Global g -> return $ Lambda.Global g
  Abstract.Con c -> return $ Lambda.Con c
  Abstract.Lit l -> return $ Lambda.Lit l
  Abstract.Pi {} -> return $ Lambda.Global "_unit_"
  Abstract.Lam h _ t s -> do
    Lambda.etaLam h (erase r t) $ toScope $ erase r $ fromScope s
  Abstract.App e1 a e2 -> Lambda.App (erase r e1) (erase r e2)
  Abstract.Case e brs -> Lambda.Case (erase r e) (eraseBranches r brs)
  where
    eraseVars hps =
        ( permFun
        , Vector.map (\(h, _) -> (h, Explicit)) hps
        )
      where
        permFun (Tele n) = Tele $ fromMaybe (error "erasure tele") $ perm Vector.! n
        perm = Vector.fromList $ fst $
          Vector.foldr (\(_, p) (xs, i) -> (Just i : xs, i + 1)) ([], 0) hps
    eraseScope = toScope . erase . fromScope
    eraseBranches (ConBranches cbrs t) = ConBranches [(c, hps', eraseScope $ mapBound permFun s)  | (c, hps, s) <- cbrs, let (permFun, hps') = eraseVars hps] (erase t)
    eraseBranches (LitBranches lbrs d) = LitBranches [(l, erase e) | (l, e) <- lbrs] (erase d)

eraseDef :: Definition Abstract v -> Definition Lambda v
eraseDef (Definition e) = Definition $ erase e
eraseDef (DataDefinition DataDef {})
  = DataDefinition $ DataDef mempty
