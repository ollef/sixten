{-# LANGUAGE OverloadedStrings #-}
module Erasure where

import Bound.Scope
import Data.Maybe
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Lambda as Lambda

type Abstract = Abstract.Expr
type Lambda = Lambda.Expr

erase :: Abstract v -> Lambda v
erase expr = case expr of
  Abstract.Var v -> Lambda.Var v
  Abstract.Global g -> Lambda.Global g
  Abstract.Con c -> Lambda.Con c
  Abstract.Lit l -> Lambda.Lit l
  Abstract.Pi {} -> Lambda.Global "_unit_"
  Abstract.Lam h a _ s
    | relevance a == Relevant -> Lambda.Lam h (Lambda.Global "TODO") $ toScope $ erase $ fromScope s
    | otherwise -> erase $ instantiate1 (error "erase") s
  Abstract.App e1 a e2
    | relevance a == Relevant -> Lambda.App (erase e1) (erase e2)
    | otherwise -> erase e1
  Abstract.Case e brs -> Lambda.Case (erase e) (eraseBranches brs)
  where
    eraseVars has =
        ( permFun
        , Vector.map (\(h, _) -> (h, ReEx)) has
        )
      where
        permFun (Tele n) = Tele $ fromMaybe (error "erasure tele") $ perm Vector.! n
        perm = Vector.fromList $ fst $
          Vector.foldr (\(_, _) (xs, i) -> (Just i : xs, i + 1)) ([], 0) has
    eraseScope = toScope . erase . fromScope
    eraseBranches (ConBranches cbrs t) = ConBranches [(c, has', eraseScope $ mapBound permFun s)  | (c, has, s) <- cbrs, let (permFun, has') = eraseVars has] (erase t)
    eraseBranches (LitBranches lbrs d) = LitBranches [(l, erase e) | (l, e) <- lbrs] (erase d)

eraseDef :: Definition Abstract v -> Definition Lambda v
eraseDef (Definition e) = Definition $ erase e
eraseDef (DataDefinition DataDef {})
  = DataDefinition $ DataDef mempty
