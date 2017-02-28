{-# LANGUAGE BangPatterns, ViewPatterns, MonadComprehensions #-}
module Analysis.Simplify where

import Bound
import Control.Monad.Identity
import Data.Bifunctor
import Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Inference.Normalise
import Syntax
import Syntax.Abstract
import Util

simplifyExpr
  :: Int
  -> Expr v
  -> Expr v
simplifyExpr !applied expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Con _ -> expr
  Lit _ -> expr
  Pi h a t s -> Pi h a (simplifyExpr 0 t) $ simplifyScope 0 s
  (lamsViewM -> Just (tele, s)) ->
    etaLams
      applied
      tele
      $ simplifyScope (max 0 $ applied - teleLength tele) s
  Lam {} -> error "simplifyExpr Lam"
  App e1 p e2 ->
    betaApp
      (simplifyExpr (applied + 1) e1)
      p
      (simplifyExpr 0 e2)
  Case e brs ->
    runIdentity
      $ chooseBranch
        (simplifyExpr 0 e)
        (simplifyBranches applied brs)
        (Identity . simplifyExpr applied)
  Let h e s -> let_ h (simplifyExpr 0 e) (simplifyScope applied s)

simplifyScope
  :: Int
  -> Scope b Expr v
  -> Scope b Expr v
simplifyScope applied = toScope . simplifyExpr applied . fromScope

simplifyBranches
  :: Int
  -> Branches c a Expr v
  -> Branches c a Expr v
simplifyBranches applied (ConBranches cbrs) = ConBranches
  [ (c, simplifyTele tele, simplifyScope applied s) | (c, tele, s) <- cbrs ]
simplifyBranches applied (LitBranches lbrs def) = LitBranches
  [(l, simplifyExpr applied e) | (l, e) <- lbrs]
  $ simplifyExpr applied def
simplifyBranches _ (NoBranches typ) = NoBranches $ simplifyExpr 0 typ

simplifyTele
  :: Telescope a Expr v
  -> Telescope a Expr v
simplifyTele tele
  = Telescope $ forTele tele $ \h a fieldScope -> (h, a, simplifyScope 0 fieldScope)

let_
  :: NameHint
  -> Expr v
  -> Scope1 Expr v
  -> Expr v
let_ h e s = case bindings s of
  _ | dupl -> Util.instantiate1 e s
  [] | term -> Util.instantiate1 e s
  [_] | term -> Util.instantiate1 e s
  _ -> Let h e s
  where
    term = terminates e
    dupl = duplicable e

simplifyDef
  :: Definition Expr v
  -> Definition Expr v
simplifyDef (Definition e)
  = Definition $ simplifyExpr 0 e
simplifyDef (DataDefinition d rep)
  = DataDefinition d $ simplifyExpr 0 rep

etaLams
  :: Int
  -> Telescope Plicitness Expr v
  -> Scope Tele Expr v
  -> Expr v
etaLams applied tele scope = case go 0 $ fromScope scope of
  Nothing -> lams tele scope
  Just (i, expr) -> lams (takeTele (len - i) tele) $ toScope expr
  where
    go i (App e a (Var (B n)))
      | n == Tele (len - i')
      , a == as Vector.! unTele n
      , B n `Set.notMember` toSet (second (const ()) <$> e)
      = case go i' e of
        Nothing | etaAllowed e i' -> Just (i', e)
        res -> res
      where
        i' = i + 1
    go _ _ = Nothing
    etaAllowed e n
      = n < len -- the resulting expression terminates since it's a lambda
      || applied >= n -- termination doesn't matter since the expression is applied anyway
      || terminatesWhenCalled e
    len = teleLength tele
    as = teleAnnotations tele

betaApp :: Expr v -> Plicitness -> Expr v -> Expr v
betaApp (Lam h a1 _ s) a2 e2 | a1 == a2 = let_ h e2 s
betaApp e1 a e2 = app e1 a e2

betaApps :: Foldable t => Expr v -> t (Plicitness, Expr v) -> Expr v
betaApps = Foldable.foldl (uncurry . betaApp)

-- | Is it cost-free to duplicate this expression?
duplicable :: Expr v -> Bool
duplicable expr = case expr of
  Var _ -> True
  Global _ -> True
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let {} -> False

terminates :: Expr v -> Bool
terminates expr = case expr of
  Var _ -> True
  Global _ -> True
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> True
  App e1 _ e2 -> terminatesWhenCalled e1 && terminates e2
  Case {} -> False
  Let _ e s -> terminates e && terminates (fromScope s)

terminatesWhenCalled :: Expr v -> Bool
terminatesWhenCalled expr = case expr of
  Var _ -> False
  Global _ -> False
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let _ e s -> terminates e && terminatesWhenCalled (fromScope s)
