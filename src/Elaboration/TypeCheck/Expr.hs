{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Expr where

import Protolude

import qualified Bound
import Data.HashSet(HashSet)
import Data.IORef
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Effect.Log as Log
import Elaboration.Constraint
import Elaboration.Constructor
import Elaboration.Match
import Elaboration.MetaVar as MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.Subtype
import Elaboration.TypeCheck.Clause
import Elaboration.TypeCheck.Literal
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Literal as Pre
import qualified Syntax.Pre.Scoped as Pre
import Util

data Expected typ
  = Infer (IORef typ) InstUntil
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> Elaborate (CoreM -> CoreM)
instExpected (Infer r instUntil) t = do
  (t', f) <- instantiateForalls t instUntil
  liftIO $ writeIORef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: HasCallStack => PreM -> Polytype -> Elaborate CoreM
checkPoly expr typ = do
  logPretty "tc.expr.context" "checkPoly context" $ Context.prettyContext prettyMeta
  logPretty "tc.expr" "checkPoly expr" $ traverse prettyVar expr
  logMeta "tc.expr" "checkPoly type" $ zonk typ
  res <- Log.indent $ checkPoly' expr typ
  logMeta "tc.expr" "checkPoly res expr" $ zonk res
  return res

checkPoly' :: PreM -> Polytype -> Elaborate CoreM
checkPoly' (Pre.SourceLoc loc e) polyType
  = located loc $ Core.SourceLoc loc <$> checkPoly' e polyType
checkPoly' expr@(Pre.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType
  = skolemise polyType (instUntilExpr expr) $ \rhoType f -> do
    e <- checkRho expr rhoType
    return $ f e

instantiateForalls
  :: Polytype
  -> InstUntil
  -> Elaborate (Rhotype, CoreM -> CoreM)
instantiateForalls typ instUntil = do
  typ' <- whnf typ
  instantiateForalls' typ' instUntil

instantiateForalls'
  :: Polytype
  -> InstUntil
  -> Elaborate (Rhotype, CoreM -> CoreM)
instantiateForalls' (Core.Pi h p t s) instUntil
  | shouldInst p instUntil = do
    v <- exists h p t
    let typ = Util.instantiate1 v s
    (result, f) <- instantiateForalls typ instUntil
    return (result, \x -> f $ Core.App x p v)
instantiateForalls' typ _ = return (typ, identity)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: PreM -> Rhotype -> Elaborate CoreM
checkRho expr typ = do
  logPretty "tc.expr.context" "checkRho context" $ Context.prettyContext prettyMeta
  logPretty "tc.expr" "checkRho expr" $ traverse prettyVar expr
  logMeta "tc.expr" "checkRho type" $ zonk typ
  res <- Log.indent $ checkRho' expr typ
  logMeta "tc.expr" "checkRho res expr" $ zonk res
  return res

checkRho' :: PreM -> Rhotype -> Elaborate CoreM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: PreM -> InstUntil -> Maybe Rhotype -> Elaborate (CoreM, Rhotype)
inferRho expr instUntil expectedAppResult = do
  logPretty "tc.expr.context" "inferRho context" $ Context.prettyContext prettyMeta
  logPretty "tc.expr" "inferRho" $ traverse prettyVar expr
  (resExpr, resType) <- Log.indent $ inferRho' expr instUntil expectedAppResult
  logMeta "tc.expr" "inferRho res expr" $ zonk resExpr
  logMeta "tc.expr" "inferRho res typ" $ zonk resType
  return (resExpr, resType)

inferRho' :: PreM -> InstUntil -> Maybe Rhotype -> Elaborate (CoreM, Rhotype)
inferRho' expr instUntil expectedAppResult = do
  ref <- liftIO $ newIORef $ panic "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instUntil) expectedAppResult
  typ <- liftIO $ readIORef ref
  return (expr', typ)

tcRho :: PreM -> Expected Rhotype -> Maybe Rhotype -> Elaborate CoreM
tcRho expr expected expectedAppResult = case expr of
  Pre.Var v -> do
    t <- Context.lookupType v
    f <- instExpected expected t
    return $ f $ Core.Var v
  Pre.Global g -> do
    let
      gn = gname g
    typ <- fetchType gn
    f <- instExpected expected typ
    return $ f $ Core.Global gn
  Pre.Lit l -> do
    let
      (e, typ) = inferLit l
    f <- instExpected expected typ
    return $ f e
  Pre.Con cons -> do
    qc <- resolveConstr cons expectedAppResult
    (_, typ) <- fetchQConstructor qc
    f <- instExpected expected typ
    return $ f $ Core.Con qc
  Pre.Pi p pat bodyScope -> do
    let
      h = patternHint pat
    typ <- existsType h
    f <- instExpected expected Builtin.Type
    Context.freshExtend (binding h p typ) $ \v -> do
      body <- matchSingle v pat bodyScope Builtin.Type checkPoly
      f <$> Core.pi_ v body
  Pre.Lam p pat bodyScope -> do
    let
      h = patternHint pat
    case expected of
      Infer {} -> do
        argType <- existsType h
        -- Creating the exisential before extending the context with the
        -- argument means that bodyType can't depend on the value of the
        -- argument. This gives us better inference, but means we only
        -- infer non-dependent functions.
        bodyType <- existsType mempty
        Context.freshExtend (binding h p argType) $ \argVar -> do
          body <- matchSingle argVar pat bodyScope bodyType checkRho
          resType <- Core.pi_ argVar bodyType
          f <- instExpected expected resType
          f <$> Core.lam argVar body
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let
          h' = h <> typeh
        Context.freshExtend (binding h' p argType) $ \argVar -> do
          let
            bodyType = instantiate1 (pure argVar) bodyTypeScope
          body <- matchSingle argVar pat bodyScope bodyType checkPoly
          fResult <$> Core.lam argVar body
  Pre.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstUntil p) expectedAppResult
    (argType, resTypeScope, f1) <- subtypeFun funType p
    let fun'' = f1 fun'
    case unusedScope resTypeScope of
      Nothing -> do
        logCategory "tc.expr" "app used scope"
        arg' <- checkPoly arg argType
        let resType = Util.instantiate1 arg' resTypeScope
        f2 <- instExpected expected resType
        return $ f2 $ Core.App fun'' p arg'
      Just resType -> do
        logCategory "tc.expr" "app unused scope"
        f2 <- instExpected expected resType
        arg' <- checkPoly arg argType
        return $ f2 $ Core.App fun'' p arg'
  Pre.Let ds scope -> tcLet ds scope expected expectedAppResult
  Pre.Case e brs -> tcBranches e brs expected expectedAppResult
  Pre.ExternCode c -> do
    c' <- mapM (\e -> fst <$> inferRho e (InstUntil Explicit) Nothing) c
    returnType <- existsType mempty
    f <- instExpected expected returnType
    return $ f $ Core.ExternCode c' returnType
  Pre.Wildcard -> do
    t <- existsType mempty
    f <- instExpected expected t
    x <- exists mempty Explicit t
    return $ f x
  Pre.SourceLoc loc e -> located loc
    $ Core.SourceLoc loc
    <$> tcRho e expected expectedAppResult

tcLet
  :: Vector (SourceLoc, NameHint, Pre.ConstantDef Pre.Expr (Bound.Var LetVar Var))
  -> Scope LetVar Pre.Expr Var
  -> Expected Rhotype
  -> Maybe Rhotype
  -> Elaborate CoreM
tcLet ds scope expected expectedAppResult = do
  bindingDefs <- forM ds $ \(loc, h, def) -> do
    typ <- existsType h
    return (binding h Explicit typ, loc, def)

  Context.freshExtends (fst3 <$> bindingDefs) $ \vars -> do
    instDefs <- forM (Vector.zip vars bindingDefs) $ \(var, (_, loc, def)) -> located loc $ do
      let instDef@(Pre.ConstantDef _ _ mtyp) = Pre.instantiateLetConstantDef pure vars def
      case mtyp of
        Just typ -> do
          typ' <- checkPoly typ Builtin.Type
          varType <- Context.lookupType var
          runUnify (unify [] varType typ') report
        Nothing -> return ()
      return (var, loc, instDef)

    ds' <- forM instDefs $ \(var, loc, def) -> located loc $ do
      varType <- Context.lookupType var
      (a, e) <- checkConstantDef def varType
      let
        set :: Elaborate a -> Elaborate a
        set = case a of
          Abstract -> identity
          Concrete -> Context.set var e
      return ((var, loc, e), set)

    body <- foldr (.) identity (snd <$> ds')
      $ tcRho (instantiateLet pure vars scope) expected expectedAppResult
    Core.let_ (fst <$> ds') body

tcBranches
  :: PreM
  -> [(SourceLoc, Pat (HashSet QConstr) Pre.Literal (PatternScope Pre.Expr Var) NameHint, PatternScope Pre.Expr Var)]
  -> Expected Rhotype
  -> Maybe Rhotype
  -> Elaborate CoreM
tcBranches expr pbrs expected expectedAppResult = do
  (expr', exprType) <- inferRho expr (InstUntil Explicit) Nothing

  case expected of
    Check resType ->
      matchBranches expr' exprType pbrs resType checkPoly

    Infer _ instUntil -> do
      resType <- existsType mempty
      res <- matchBranches expr' exprType pbrs resType $ \body bodyType -> do
        (body', bodyType') <- inferRho body instUntil expectedAppResult
        f <- subtype bodyType' bodyType
        return $ f body'
      f <- instExpected expected resType
      return $ f res
