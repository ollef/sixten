{-# LANGUAGE MonadComprehensions #-}
module Inference.Subtype where

import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Inference.Constraint
import Analysis.Simplify
import Inference.MetaVar
import Inference.Monad
import Inference.Unify
import MonadContext
import Syntax
import Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import Util
import Util.Tsil
import VIX

--------------------------------------------------------------------------------
-- | deepSkolemise t1 = (t2, f) => f : t2 -> t1
--
-- Deep skolemisation. Like skolemise, but peels off quantifiers under pis,
-- e.g. the `b` in `Int -> forall b. b -> b`
deepSkolemise
  :: Polytype
  -> (Rhotype -> (CoreM -> CoreM) -> Infer a)
  -> Infer a
deepSkolemise t1 k
  = deepSkolemiseInner t1 mempty $ \vs t2 f -> k t2 $ f . lams vs

deepSkolemiseInner
  :: Polytype
  -> HashSet FreeV
  -> (Vector FreeV -> Rhotype -> (CoreM -> CoreM) -> Infer a)
  -> Infer a
deepSkolemiseInner typ argsToPass k = do
  typ' <- whnf typ
  deepSkolemiseInner' typ' argsToPass k

deepSkolemiseInner'
  :: Polytype
  -> HashSet FreeV
  -> (Vector FreeV -> Rhotype -> (CoreM -> CoreM) -> Infer a)
  -> Infer a
deepSkolemiseInner' typ@(Pi h p t resScope) argsToPass k = case p of
  Explicit -> do
    y <- forall h p t
    withVar y $ do
      let resType = Util.instantiate1 (pure y) resScope
      deepSkolemiseInner resType (HashSet.insert y argsToPass) $ \vs resType' f -> k
        vs
        (pi_ y resType')
        (\x -> lam y $ f $ lams vs $ betaApp (betaApps x $ (\v -> (varData v, pure v)) <$> vs) p $ pure y)
  Implicit -> implicitCase
  Constraint -> implicitCase
  where
    implicitCase
      -- If the type mentions any dependent arguments that we are going to
      -- "pass", (e.g. when trying to pull `b` above `A` in `(A : Type) -> forall
      -- (b : A). Int`), we have to bail out.
      | HashSet.size (HashSet.intersection (toHashSet t) argsToPass) > 0 = k mempty typ id
      | otherwise = do
        y <- forall h p t
        withVar y $ do
          let resType = Util.instantiate1 (pure y) resScope
          deepSkolemiseInner resType argsToPass $ \vs resType' f -> k
            (Vector.cons y vs)
            resType'
            (\x -> lam y $ f $ betaApp x p $ pure y)
deepSkolemiseInner' typ _ k = k mempty typ id

--------------------------------------------------------------------------------
-- | skolemise t1 = (t2, f) => f : t2 -> t1
--
-- Peel off quantifiers from the given type, instantiating them with skolem
-- variables ('forall'), and return (to the given continuation function) a
-- function that takes a term of the peeled type and produces a term of the
-- unpeeled type.
skolemise
  :: Polytype
  -> InstUntil
  -> (Rhotype -> (CoreM -> CoreM) -> Infer a)
  -> Infer a
skolemise typ instUntil k = do
  typ' <- whnf typ
  skolemise' typ' instUntil k

skolemise'
  :: Polytype
  -> InstUntil
  -> (Rhotype -> (CoreM -> CoreM) -> Infer a)
  -> Infer a
skolemise' (Pi h p t resScope) instUntil k
  | shouldInst p instUntil = do
    v <- forall h p t
    let resType = Util.instantiate1 (pure v) resScope
    withVar v $ skolemise resType instUntil $ \resType' f -> do
      let f' x = lam v $ f x
      k resType' f'
skolemise' typ _ k = k typ id

instUntilExpr :: Pre.Expr v -> InstUntil
instUntilExpr (Pre.Lam p _ _) = InstUntil p
instUntilExpr _ = InstUntil Explicit

--------------------------------------------------------------------------------
-- Subtyping/subsumption
-- | subtype t1 t2 = f => f : t1 -> t2
subtype :: Polytype -> Polytype -> Infer (CoreM -> CoreM)
subtype typ1 typ2 = indentLog $ do
  logMeta 30 "subtype t1" typ1
  logMeta 30 "        t2" typ2
  deepSkolemise typ2 $ \rho f1 -> do
    f2 <- subtypeRho typ1 rho $ InstUntil Explicit
    return $ f1 . f2

subtypeRho :: Polytype -> Rhotype -> InstUntil -> Infer (CoreM -> CoreM)
subtypeRho typ1 typ2 instUntil = do
  logMeta 30 "subtypeRho t1" typ1
  logMeta 30 "           t2" typ2
  indentLog $ do
    typ1' <- whnf typ1
    typ2' <- whnf typ2
    subtypeRho' typ1' typ2' instUntil

subtypeRho' :: Polytype -> Rhotype -> InstUntil -> Infer (CoreM -> CoreM)
subtypeRho' (Pi h1 p1 argType1 retScope1) (Pi h2 p2 argType2 retScope2) _
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p1 argType2
    let v1 = f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- withVar v2 $ subtypeRho retType1 retType2 $ InstUntil Explicit
    return $ \x -> lam v2 $ f2 (App x p1 v1)
subtypeRho' (Pi h p t s) typ2 instUntil | shouldInst p instUntil = do
  v <- exists h p t
  f <- subtypeRho (Util.instantiate1 v s) typ2 instUntil
  return $ \x -> f $ App x p v
subtypeRho' typ1 typ2 _ = do
  unify [] typ1 typ2
  return id

-- | funSubtypes typ ps = (ts, retType, f) => f : (ts -> retType) -> typ
funSubtypes
  :: Rhotype
  -> Vector Plicitness
  -> Infer
    ( Telescope Plicitness (Expr MetaVar) FreeV
    , Scope TeleVar (Expr MetaVar) FreeV
    , Vector (CoreM -> CoreM)
    )
funSubtypes startType plics = go plics startType mempty mempty
  where
    go ps typ vs fs
      | Vector.null ps = do
        let vars = toVector vs
            tele = varTelescope vars
            typeScope = abstract (teleAbstraction vars) typ
        return (tele, typeScope, toVector fs)
      | otherwise = do
        let p = Vector.head ps
        (h, argType, resScope, f) <- funSubtype typ p
        v <- forall h p argType
        withVar v $ go
          (Vector.tail ps)
          (Util.instantiate1 (pure v) resScope)
          (Snoc vs v)
          (Snoc fs f)

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> Infer (NameHint, Rhotype, Scope1 (Expr MetaVar) FreeV, CoreM -> CoreM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> Infer (NameHint, Rhotype, Scope1 (Expr MetaVar) FreeV, CoreM -> CoreM)
funSubtype' (Pi h p t s) p' | p == p' = return (h, t, s, id)
funSubtype' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtypeRho' (Pi mempty p argType resScope) typ $ InstUntil p
  return (mempty, argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> Infer (Rhotype, Scope1 (Expr MetaVar) FreeV, CoreM -> CoreM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> Infer (Rhotype, Scope1 (Expr MetaVar) FreeV, CoreM -> CoreM)
subtypeFun' (Pi _ p t s) p' | p == p' = return (t, s, id)
subtypeFun' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtype typ $ Pi mempty p argType resScope
  return (argType, resScope, f)
