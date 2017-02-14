{-# LANGUAGE BangPatterns, ViewPatterns, MonadComprehensions #-}
module Analysis.Simplify where

import Bound
import Data.Bifunctor
import Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Syntax
import Syntax.Abstract
import Util

simplifyExpr :: Eq a => Int -> Expr a v -> Expr a v
simplifyExpr !applied expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Con _ -> expr
  Lit _ -> expr
  Pi h a t s -> Pi h a (simplifyExpr 0 t) $ simplifyScope 0 s
  (lamsViewM -> Just (tele, s)) -> etaLams applied tele $ simplifyScope (max 0 $ applied - teleLength tele) s
  Lam {} -> error "simplifyExpr Lam"
  App e1 p e2 -> betaApp (simplifyExpr (applied + 1) e1) p (simplifyExpr 0 e2)
  -- TODO do something clever here
  Case e brs -> Case (simplifyExpr 0 e) $ simplifyBranches applied brs
  Let h a e s -> let_ h a (simplifyExpr 0 e) (simplifyScope applied s)

-- \x y. f x y

simplifyScope :: Eq a => Int -> Scope b (Expr a) v -> Scope b (Expr a) v
simplifyScope applied = toScope . simplifyExpr applied . fromScope

simplifyBranches
  :: Eq a
  => Int
  -> Branches c a (Expr a) v
  -> Branches c a (Expr a) v
simplifyBranches applied (ConBranches cbrs) = ConBranches
  [ (c, simplifyTele tele, simplifyScope applied s) | (c, tele, s) <- cbrs ]
simplifyBranches applied (LitBranches lbrs def) = LitBranches
  [(l, simplifyExpr applied e) | (l, e) <- lbrs]
  $ simplifyExpr applied def
simplifyBranches _ (NoBranches typ) = NoBranches $ simplifyExpr 0 typ

simplifyTele
  :: Eq a
  => Telescope a (Expr a) v
  -> Telescope a (Expr a) v
simplifyTele tele
  = Telescope $ forTele tele $ \h a fieldScope -> (h, a, simplifyScope 0 fieldScope)

let_
  :: Eq a
  => NameHint
  -> a
  -> Expr a v
  -> Scope1 (Expr a) v
  -> Expr a v
let_ h a e s = case bindings s of
  _ | dupl -> Util.instantiate1 e s
  [] | term -> Util.instantiate1 e s
  [_] | term -> Util.instantiate1 e s
  _ -> Let h a e s
  where
    term = terminates e
    dupl = duplicable e

simplifyDef
  :: Eq a
  => Definition (Expr a) v
  -> Definition (Expr a) v
-- This is to avoid eta-reducing e.g. `loop = \x. loop x`
simplifyDef (Definition (Lam h a t s))
  = Definition $ Lam h a (simplifyExpr 0 t) $ simplifyScope 0 s
simplifyDef (Definition e)
  = Definition $ simplifyExpr 0 e
simplifyDef def@(DataDefinition _)
  = def

etaLams
  :: Eq a
  => Int
  -> Telescope a (Expr a) v
  -> Scope Tele (Expr a) v
  -> Expr a v
etaLams applied tele scope = case go 0 $ fromScope scope of
  Nothing -> lams tele scope
  Just (i, expr) -> lams (takeTele (len - i - 1) tele) $ toScope expr
  where
    go i (App e a (Var (B n)))
      | n == Tele (len - i - 1)
      , a == as Vector.! unTele n
      , B n `Set.notMember` toSet (second (const ()) <$> e)
      = case go (i + 1) e of
        Nothing | etaAllowed i e -> Just (i, e)
        res -> res
    go _ _ = Nothing
    etaAllowed i e
      = i < len -- the resulting expression terminates since it's a lambda
      || applied >= i -- termination doesn't matter since the expression is applied anyway
      || terminates e
    len = teleLength tele
    as = teleAnnotations tele

-- (\x y. nonterm x y) a -/-> (\x. nonterm x) a
-- (\x y. nonterm x y) a b --> nonterm a b

betaApp :: Eq a => Expr a v -> a -> Expr a v -> Expr a v
betaApp (Lam h a1 _ s) a2 e2 | a1 == a2 = let_ h a1 e2 s
betaApp e1 a e2 = app e1 a e2

betaApps :: (Eq a, Foldable t) => Expr a v -> t (a, Expr a v) -> Expr a v
betaApps = Foldable.foldl (uncurry . betaApp)

-- | Is it cost-free to duplicate this expression?
duplicable :: Expr a v -> Bool
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

terminates :: Expr a v -> Bool
terminates expr = case expr of
  Var _ -> True
  Global _ -> True
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> True
  App {} -> False
  Case {} -> False
  Let _ _ e s -> terminates e && terminates (fromScope s)
