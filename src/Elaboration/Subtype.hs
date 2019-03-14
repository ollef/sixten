{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
module Elaboration.Subtype where

import Protolude

import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Elaboration.Constraint
import qualified Builtin.Names as Builtin
import Effect
import qualified Effect.Context as Context
import Effect.Log as Log
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.Unify
import Syntax
import Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import Util
import Util.Tsil

type Subtype = ExceptT Error

runSubtype :: Monad m => Subtype m a -> (Error -> m a) -> m a
runSubtype = runUnify

--------------------------------------------------------------------------------
-- | deepSkolemise t1 = (t2, f) => f : t2 -> t1
--
-- Deep skolemisation. Like skolemise, but peels off quantifiers under pis,
-- e.g. the `b` in `Int -> forall b. b -> b`
deepSkolemise
  :: MonadElaborate m
  => Polytype
  -> (Rhotype -> (CoreM -> CoreM) -> m a)
  -> m a
deepSkolemise t1 k
  = deepSkolemiseInner t1 mempty $ \vs t2 f -> do
    ctx <- getContext
    k t2 $ \x -> f $ lams vs x ctx

deepSkolemiseInner
  :: MonadElaborate m
  => Polytype
  -> HashSet Var
  -> (Vector Var -> Rhotype -> (CoreM -> CoreM) -> m a)
  -> m a
deepSkolemiseInner typ argsToPass k = do
  typ' <- whnf typ
  deepSkolemiseInner' typ' argsToPass k

deepSkolemiseInner'
  :: MonadElaborate m
  => Polytype
  -> HashSet Var
  -> (Vector Var -> Rhotype -> (CoreM -> CoreM) -> m a)
  -> m a
deepSkolemiseInner' typ@(Pi h p t resScope) argsToPass k = case p of
  Explicit ->
    Context.freshExtend (binding h p t) $ \y -> do
      let resType = Util.instantiate1 (pure y) resScope
      deepSkolemiseInner resType (HashSet.insert y argsToPass) $ \vs resType' f -> do
        ctx <- getContext
        k
          vs
          (pi_ y resType' ctx)
          (\x -> lam y (f $ lams vs (App (apps x $ (\v -> (Context.lookupPlicitness v ctx, pure v)) <$> vs) p $ pure y) ctx) ctx)
  Implicit -> implicitCase
  Constraint -> implicitCase
  where
    implicitCase
      -- If the type mentions any dependent arguments that we are going to
      -- "pass", (e.g. when trying to pull `b` above `A` in `(A : Type) -> forall
      -- (b : A). Int`), we have to bail out.
      | HashSet.size (HashSet.intersection (toHashSet t) argsToPass) > 0 = k mempty typ identity
      | otherwise =
        Context.freshExtend (binding h p t) $ \y -> do
          let resType = Util.instantiate1 (pure y) resScope
          deepSkolemiseInner resType argsToPass $ \vs resType' f -> do
            ctx <- getContext
            k
              (Vector.cons y vs)
              resType'
              (\x -> lam y (f $ App x p $ pure y) ctx)
deepSkolemiseInner' typ _ k = k mempty typ identity

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
  -> (Rhotype -> (CoreM -> CoreM) -> Elaborate a)
  -> Elaborate a
skolemise typ instUntil k = do
  typ' <- whnf typ
  skolemise' typ' instUntil k

skolemise'
  :: Polytype
  -> InstUntil
  -> (Rhotype -> (CoreM -> CoreM) -> Elaborate a)
  -> Elaborate a
skolemise' (Pi h p t resScope) instUntil k
  | shouldInst p instUntil =
    Context.freshExtend (binding h p t) $ \v -> do
      let resType = Util.instantiate1 (pure v) resScope
      skolemise resType instUntil $ \resType' f -> do
        ctx <- getContext
        let f' x = lam v (f x) ctx
        k resType' f'
skolemise' typ _ k = k typ identity

instUntilExpr :: Pre.Expr v -> InstUntil
instUntilExpr (Pre.Lam p _ _) = InstUntil p
instUntilExpr _ = InstUntil Explicit

--------------------------------------------------------------------------------
-- Subtyping/subsumption
-- | subtype t1 t2 = f => f : t1 -> t2
subtype :: MonadElaborate m => Polytype -> Polytype -> m (CoreM -> CoreM)
subtype typ1 typ2
  = runSubtype (subtypeE typ1 typ2) $ \err -> do
    report err
    return $ const $ Builtin.Fail typ2

subtypeE
  :: (MonadElaborate m, MonadError Error m)
  => Polytype
  -> Polytype
  -> m (CoreM -> CoreM)
subtypeE typ1 typ2 = Log.indent $ do
  logMeta "tc.subtype" "subtypeE t1" $ zonk typ1
  logMeta "tc.subtype" "         t2" $ zonk typ2
  deepSkolemise typ2 $ \rho f1 -> do
    f2 <- subtypeRhoE typ1 rho $ InstUntil Explicit
    return $ f1 . f2

subtypeRhoE
  :: (MonadElaborate m, MonadError Error m)
  => Polytype
  -> Rhotype
  -> InstUntil
  -> m (CoreM -> CoreM)
subtypeRhoE typ1 typ2 instUntil = do
  logMeta "tc.subtype" "subtypeRhoE t1" $ zonk typ1
  logMeta "tc.subtype" "            t2" $ zonk typ2
  Log.indent $ do
    typ1' <- whnf typ1
    typ2' <- whnf typ2
    subtypeRhoE' typ1' typ2' instUntil

subtypeRho'
  :: MonadElaborate m
  => Polytype
  -> Rhotype
  -> InstUntil
  -> m (CoreM -> CoreM)
subtypeRho' typ1 typ2 instUntil
  = runSubtype (subtypeRhoE' typ1 typ2 instUntil) $ \err -> do
    report err
    return $ const $ Builtin.Fail typ2

subtypeRhoE'
  :: (MonadElaborate m, MonadError Error m)
  => Polytype
  -> Rhotype
  -> InstUntil
  -> m (CoreM -> CoreM)
subtypeRhoE' (Pi h1 p1 argType1 retScope1) (Pi h2 p2 argType2 retScope2) _
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtypeE argType2 argType1
    Context.freshExtend (binding h p1 argType2) $ \v2 -> do
      let v1 = f1 $ pure v2
      let retType1 = Util.instantiate1 v1 retScope1
          retType2 = Util.instantiate1 (pure v2) retScope2
      f2 <- subtypeRhoE retType1 retType2 $ InstUntil Explicit
      ctx <- getContext
      return $ \x -> lam v2 (f2 $ App x p1 v1) ctx
subtypeRhoE' (Pi h p t s) typ2 instUntil | shouldInst p instUntil = do
  v <- exists h p t
  f <- subtypeRhoE (Util.instantiate1 v s) typ2 instUntil
  return $ \x -> f $ App x p v
subtypeRhoE' typ1 typ2 _ = do
  unify [] typ1 typ2
  return identity

-- | funSubtypes typ ps = (ts, retType, f) => f : (ts -> retType) -> typ
funSubtypes
  :: Rhotype
  -> Vector Plicitness
  -> Elaborate
    ( Telescope (Expr MetaVar) Var
    , Scope TeleVar (Expr MetaVar) Var
    , Vector (CoreM -> CoreM)
    )
funSubtypes startType plics = go plics startType mempty mempty
  where
    go ps typ vs fs
      | Vector.null ps = do
        let vars = toVector vs
        tele <- varTelescope vars
        let typeScope = abstract (teleAbstraction vars) typ
        return (tele, typeScope, toVector fs)
      | otherwise = do
        let p = Vector.head ps
        (h, argType, resScope, f) <- funSubtype typ p
        Context.freshExtend (binding h p argType) $ \v ->
          go
            (Vector.tail ps)
            (Util.instantiate1 (pure v) resScope)
            (Snoc vs v)
            (Snoc fs f)

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> Elaborate (NameHint, Rhotype, Scope1 (Expr MetaVar) Var, CoreM -> CoreM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> Elaborate (NameHint, Rhotype, Scope1 (Expr MetaVar) Var, CoreM -> CoreM)
funSubtype' (Pi h p t s) p' | p == p' = return (h, t, s, identity)
funSubtype' typ p = do
  (argType, resScope) <- existsPi
  f <- subtypeRho' (Pi mempty p argType resScope) typ $ InstUntil p
  return (mempty, argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> Elaborate (Rhotype, Scope1 (Expr MetaVar) Var, CoreM -> CoreM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> Elaborate (Rhotype, Scope1 (Expr MetaVar) Var, CoreM -> CoreM)
subtypeFun' (Pi _ p t s) p' | p == p' = return (t, s, identity)
subtypeFun' typ p = do
  (argType, resScope) <- existsPi
  f <- subtype typ $ Pi mempty p argType resScope
  return (argType, resScope, f)

existsPi :: Elaborate (CoreM, Scope1 (Expr MetaVar) Var)
existsPi = do
  argType <- existsType mempty
  resType <- existsType mempty
  return (argType, abstractNone resType)
