{-# LANGUAGE ViewPatterns, MonadComprehensions #-}
module Simplify where

import Bound
import Data.Bifunctor
import Data.Foldable as Foldable
import qualified Data.Set as Set

import Syntax
import Syntax.Abstract
import Util

simplifyExpr :: Eq a => Bool -> Expr a v -> Expr a v
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

simplifyScope :: Eq a => Bool -> Scope b (Expr a) v -> Scope b (Expr a) v
simplifyScope applied = toScope . simplifyExpr applied . fromScope

simplifyBranches
  :: Eq a
  => Bool
  -> Branches c a (Expr a) v
  -> Branches c a (Expr a) v
simplifyBranches applied (ConBranches cbrs) = ConBranches
  [ let tele' = Telescope $ forTele tele $ \h a fieldScope -> (h, a, simplifyScope False fieldScope)
        s' = simplifyScope applied s
    in (c, tele', s')
  | (c, tele, s) <- cbrs
  ]
simplifyBranches applied (LitBranches lbrs def) = LitBranches
  [(l, simplifyExpr applied e) | (l, e) <- lbrs]
  $ simplifyExpr applied def
simplifyBranches _ (NoBranches typ) = NoBranches $ simplifyExpr False typ

simplifyDef
  :: Eq a
  => Definition (Expr a) v
  -> Definition (Expr a) v
-- This is to avoid eta-reducing e.g. `loop = \x. loop x`
simplifyDef (Definition (Lam h a t s))
  = Definition $ Lam h a (simplifyExpr False t) $ simplifyScope False s
simplifyDef (Definition e)
  = Definition $ simplifyExpr False e
simplifyDef def@(DataDefinition _)
  = def

etaLam
  :: Eq a
  => Bool -- ^ Will we be applied anyway (such that termination doesn't matter)?
  -> NameHint
  -> a
  -> Expr a v
  -> Scope1 (Expr a) v
  -> Expr a v
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
etaLam _ h p t s = Lam h p t s

betaApp :: Eq a => Expr a v -> a -> Expr a v -> Expr a v
betaApp e1@(Lam _ a1 _ s) a2 e2
  | a1 == a2 = case bindings s of
    _ | duplicable e2 -> Util.instantiate1 e2 s
    []  -> Util.instantiate1 e2 s
    [_] -> Util.instantiate1 e2 s
    _   -> app e1 a1 e2
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
