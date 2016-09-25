{-# LANGUAGE ViewPatterns #-}
module Simplify where

import Bound
import Data.Bifunctor
import Data.Foldable as Foldable
import qualified Data.Set as Set

import Syntax
import Syntax.Abstract
import Util

simplifyExpr :: Bool -> Expr v -> Expr v
simplifyExpr applied expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Con _ -> expr
  Lit _ -> expr
  Pi h a t s -> Pi h a (simplifyExpr False t) $ simplifyScope False s
  Lam h a t s -> etaLam applied h a (simplifyExpr False t) $ simplifyScope False s
  App e1 p e2 -> betaApp (simplifyExpr True e1) p (simplifyExpr False e2)
  -- TODO do something clever here
  Case e brs -> Case (simplifyExpr False e) $ simplifyBranches applied brs

simplifyScope :: Bool -> Scope b Expr v -> Scope b Expr v
simplifyScope applied = toScope . simplifyExpr applied . fromScope

simplifyBranches
  :: Bool
  -> Branches c Expr v
  -> Branches c Expr v
simplifyBranches applied (ConBranches cbrs typ) = ConBranches
  [ let tele' = Telescope $ forTele tele $ \h a fieldScope -> (h, a, simplifyScope False fieldScope)
        s' = simplifyScope applied s
    in (c, tele', s')
  | (c, tele, s) <- cbrs
  ] typ
simplifyBranches applied (LitBranches lbrs def) = LitBranches
  [(l, simplifyExpr applied e) | (l, e) <- lbrs]
  $ simplifyExpr applied def

simplifyDef
  :: Definition Expr v
  -> Definition Expr v
-- This is to avoid eta-reducing e.g. `loop = \x. loop x`
simplifyDef (Definition (Lam h a t s))
  = Definition $ Lam h a (simplifyExpr False t) $ simplifyScope False s
simplifyDef (Definition e)
  = Definition $ simplifyExpr False e
simplifyDef def@(DataDefinition _)
  = def

etaLam
  :: Bool -- ^ Will we be applied anyway (such that termination doesn't matter)?
  -> NameHint
  -> Annotation
  -> Expr v
  -> Scope1 Expr v
  -> Expr v
etaLam applied _ a _ (fromScope -> App e a' (Var (B ())))
  | B () `Set.notMember` toSet (second (const ()) <$> e)
  , a == a'
  , applied || terminates e
  = unvar (error "etaLam impossible") id <$> e
  where
    terminates expr = case expr of
      Var _ -> True
      Global _ -> True
      Con _ -> True
      Lit _ -> True
      Pi {} -> True
      Lam {} -> True
      App {} -> False
      Case {} -> False -- TODO Maybe do something more clever?
etaLam _ h a t s = Lam h a t s

betaApp :: Expr v -> Annotation -> Expr v -> Expr v
betaApp e1@(lamView -> Just (_, p1, _, s)) p2 e2
  | p1 == p2 = case bindings s of
    _ | duplicable e2 -> instantiate1 e2 s
    []  -> instantiate1 e2 s
    [_] -> instantiate1 e2 s
    _   -> app e1 p1 e2
betaApp e1 p e2 = app e1 p e2

betaApps :: Foldable t => Expr v -> t (Annotation, Expr v) -> Expr v
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
