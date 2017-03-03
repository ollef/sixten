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
  :: (Name -> Bool)
  -> Int
  -> Expr v
  -> Expr v
simplifyExpr glob !applied expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Con _ -> expr
  Lit _ -> expr
  Pi h a t s -> Pi h a (simplifyExpr glob 0 t) $ simplifyScope glob 0 s
  (lamsViewM -> Just (tele, s)) ->
    etaLams
      glob
      applied
      tele
      $ simplifyScope glob (max 0 $ applied - teleLength tele) s
  Lam {} -> error "simplifyExpr Lam"
  App e1 p e2 ->
    betaApp
      (simplifyExpr glob (applied + 1) e1)
      p
      (simplifyExpr glob 0 e2)
  Case e brs ->
    runIdentity
      $ chooseBranch
        (simplifyExpr glob 0 e)
        (simplifyBranches glob applied brs)
        (Identity . simplifyExpr glob applied)
  Let h e s -> let_ glob h (simplifyExpr glob 0 e) (simplifyScope glob applied s)

simplifyScope
  :: (Name -> Bool)
  -> Int
  -> Scope b Expr v
  -> Scope b Expr v
simplifyScope glob applied = toScope . simplifyExpr glob applied . fromScope

simplifyBranches
  :: (Name -> Bool)
  -> Int
  -> Branches c a Expr v
  -> Branches c a Expr v
simplifyBranches glob applied (ConBranches cbrs) = ConBranches
  [ (c, simplifyTele glob tele, simplifyScope glob applied s) | (c, tele, s) <- cbrs ]
simplifyBranches glob applied (LitBranches lbrs def) = LitBranches
  [(l, simplifyExpr glob applied e) | (l, e) <- lbrs]
  $ simplifyExpr glob applied def
simplifyBranches glob _ (NoBranches typ) = NoBranches $ simplifyExpr glob 0 typ

simplifyTele
  :: (Name -> Bool)
  -> Telescope a Expr v
  -> Telescope a Expr v
simplifyTele glob tele
  = Telescope $ forTele tele $ \h a fieldScope -> (h, a, simplifyScope glob 0 fieldScope)

let_
  :: (Name -> Bool)
  -> NameHint
  -> Expr v
  -> Scope1 Expr v
  -> Expr v
let_ glob h e s = case bindings s of
  _ | dupl -> Util.instantiate1 e s
  [] | term -> Util.instantiate1 e s
  [_] | term -> Util.instantiate1 e s
  _ -> Let h e s
  where
    term = terminates glob e
    dupl = duplicable e

simplifyDef
  :: (Name -> Bool)
  -> Definition Expr v
  -> Definition Expr v
simplifyDef glob (Definition e)
  = Definition $ simplifyExpr glob 0 e
simplifyDef glob (DataDefinition d rep)
  = DataDefinition d $ simplifyExpr glob 0 rep

etaLams
  :: (Name -> Bool)
  -> Int
  -> Telescope Plicitness Expr v
  -> Scope Tele Expr v
  -> Expr v
etaLams glob applied tele scope = case go 0 $ fromScope scope of
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
      || terminates glob e -- Use glob for termination to e.g. avoid making `loop = loop` out of `loop x = loop x`
    len = teleLength tele
    as = teleAnnotations tele

betaApp ::  Expr v -> Plicitness -> Expr v -> Expr v
betaApp (Lam h a1 _ s) a2 e2 | a1 == a2 = let_ (const True) h e2 s
betaApp e1 a e2 = app e1 a e2

betaApps
  :: Foldable t
  => Expr v
  -> t (Plicitness, Expr v)
  -> Expr v
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

terminates :: (Name -> Bool) -> Expr v -> Bool
terminates glob expr = case expr of
  Var _ -> True
  Global n -> glob n
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> True
  App e1 _ e2 -> terminatesWhenCalled glob e1 && terminates glob e2
  Case {} -> False
  Let _ e s -> terminates glob e && terminates glob (fromScope s)

terminatesWhenCalled :: (Name -> Bool) -> Expr v -> Bool
terminatesWhenCalled glob expr = case expr of
  Var _ -> False
  Global _ -> False
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let _ e s -> terminates glob e && terminatesWhenCalled glob (fromScope s)
