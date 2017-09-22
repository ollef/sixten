{-# LANGUAGE BangPatterns, ViewPatterns, MonadComprehensions #-}
module Analysis.Simplify where

import Bound
import Data.Bifunctor
import Data.Foldable as Foldable
import Data.Functor.Identity
import Data.Maybe
import Data.Monoid
import qualified Data.MultiSet as MultiSet
import qualified Data.Set as Set
import qualified Data.Vector as Vector

import Inference.Normalise
import Syntax
import Syntax.Abstract hiding (let_)
import Util

simplifyExpr
  :: (QName -> Bool)
  -> Int
  -> Expr v
  -> Expr v
simplifyExpr glob !applied expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Con _ -> expr
  Lit _ -> expr
  Pi h a t s -> Pi h a (simplifyExpr glob 0 t) $ hoist (simplifyExpr glob 0) s
  (lamsViewM -> Just (tele, s)) ->
    etaLams
      glob
      applied
      tele
      $ hoist (simplifyExpr glob $ max 0 $ applied - teleLength tele) s
  Lam {} -> error "simplifyExpr Lam"
  App e1 p e2 ->
    betaApp
      (simplifyExpr glob (applied + 1) e1)
      p
      (simplifyExpr glob 0 e2)
  Case e brs retType ->
    runIdentity
      $ chooseBranch
        (simplifyExpr glob 0 e)
        (hoist (simplifyExpr glob applied) brs)
        (simplifyExpr glob 0 retType)
        (Identity . simplifyExpr glob applied)
  Let ds s -> letRec glob (hoist (simplifyExpr glob 0) ds) $ hoist (simplifyExpr glob applied) s
  ExternCode c retType ->
    ExternCode
      (simplifyExpr glob 0 <$> c)
      (simplifyExpr glob 0 retType)

-- TODO: Inlining can expose more simplification opportunities that aren't exploited.
letRec
  :: (QName -> Bool)
  -> LetRec Expr v
  -> Scope LetVar Expr v
  -> Expr v
letRec glob ds scope
  | Vector.null ds' = instantiate (error "letRec empty") scope'
  | otherwise = Let (LetRec ds') scope'
  where
    occs = MultiSet.fromList (bindings scope)
      <> foldMap (MultiSet.fromList . bindings) (letBodies ds)
    dsFilter = iforLet ds $ \i h s t -> do
      let e = fromScope s
          v = LetVar i
          s' = rebind rebinding s
      if duplicable e || MultiSet.occur v occs <= 1 && terminates glob e
        then (mempty, s')
        else (pure (v, LetBinding h s' t), Scope $ pure $ B $ permute v)
    rebinding (LetVar v) = snd $ dsFilter Vector.! v
    oldVarsNewDs = Vector.concatMap fst dsFilter
    permute = LetVar . fromJust . hashedElemIndex (fst <$> oldVarsNewDs)

    ds' = snd <$> oldVarsNewDs
    scope' = rebind rebinding scope

let_
  :: (QName -> Bool)
  -> NameHint
  -> Expr v
  -> Type v
  -> Scope1 Expr v
  -> Expr v
let_ glob h e t s
  = letRec
    glob
    (LetRec $ pure $ LetBinding h (abstractNone e) t)
    (mapBound (\() -> 0) s)

simplifyDef
  :: (QName -> Bool)
  -> Definition Expr v
  -> Definition Expr v
simplifyDef glob = hoist $ simplifyExpr glob 0

etaLams
  :: (QName -> Bool)
  -> Int
  -> Telescope Plicitness Expr v
  -> Scope TeleVar Expr v
  -> Expr v
etaLams glob applied tele scope = case go 0 $ fromScope scope of
  Nothing -> lams tele scope
  Just (i, expr) -> lams (takeTele (len - i) tele) $ toScope expr
  where
    go i (App e a (Var (B n)))
      | n == TeleVar (len - i')
      , a == as Vector.! unTeleVar n
      , B n `Set.notMember` toSet (second (const ()) <$> e)
      = case go i' e of
        Nothing | etaAllowed e i' -> Just (i', e)
        res -> res
      where
        i' = i + 1
    go _ _ = Nothing
    etaAllowed e n
      = applied >= n -- termination doesn't matter since the expression is applied anyway
      || terminates glob e -- Use glob for termination to e.g. avoid making `loop = loop` out of `loop x = loop x`
    len = teleLength tele
    as = teleAnnotations tele

betaApp ::  Expr v -> Plicitness -> Expr v -> Expr v
betaApp (Lam h a1 t s) a2 e2 | a1 == a2 = let_ (const True) h e2 t s
betaApp e1 a e2 = App e1 a e2

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
  ExternCode {} -> False

terminates :: (QName -> Bool) -> Expr v -> Bool
terminates glob expr = case expr of
  Var _ -> True
  Global n -> glob n
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> True
  App e1 _ e2 -> terminatesWhenCalled glob e1 && terminates glob e2
  Case {} -> False
  Let ds s -> all (terminates glob) (fromScope <$> letBodies ds) && terminates glob (fromScope s)
  ExternCode {} -> False

terminatesWhenCalled :: (QName -> Bool) -> Expr v -> Bool
terminatesWhenCalled glob expr = case expr of
  Var _ -> False
  Global _ -> False
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let ds s -> all (terminates glob) (fromScope <$> letBodies ds) && terminatesWhenCalled glob (fromScope s)
  ExternCode {} -> False
