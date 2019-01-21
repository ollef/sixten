{-# LANGUAGE OverloadedStrings #-}
module Elaboration.TypeCheck.Expr where

import Protolude

import Data.HashSet(HashSet)
import Data.IORef
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Analysis.Simplify
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
import Elaboration.TypeCheck.Pattern
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
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
checkPoly :: PreM -> Polytype -> Elaborate CoreM
checkPoly expr typ = do
  logPretty "tc.expr" "checkPoly expr" $ pure $ pretty <$> expr
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
    return (result, \x -> f $ betaApp x p v)
instantiateForalls' typ _ = return (typ, identity)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: PreM -> Rhotype -> Elaborate CoreM
checkRho expr typ = do
  logPretty "tc.expr" "checkRho expr" $ pure $ pretty <$> expr
  logMeta "tc.expr" "checkRho type" $ zonk typ
  res <- Log.indent $ checkRho' expr typ
  logMeta "tc.expr" "checkRho res expr" $ zonk res
  return res

checkRho' :: PreM -> Rhotype -> Elaborate CoreM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: PreM -> InstUntil -> Maybe Rhotype -> Elaborate (CoreM, Rhotype)
inferRho expr instUntil expectedAppResult = do
  logPretty "tc.expr" "inferRho" $ pure $ pretty <$> expr
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
    typ <- fetchQConstructor qc
    f <- instExpected expected typ
    return $ f $ Core.Con qc
  Pre.Pi p pat bodyScope ->
    inferPat p pat $ \pat' _ patVars patType -> do
      let
        body = instantiatePattern pure (boundPatVars patVars) bodyScope
        h = Pre.patternHint pat
      body' <- checkPoly body Builtin.Type
      f <- instExpected expected Builtin.Type
      Context.freshExtend (binding h p patType) $ \x -> do
        body'' <- matchSingle (pure x) pat' body' Builtin.Type
        return $ f $ Core.pi_ x body''
  Pre.Lam p pat bodyScope -> do
    let
      h = Pre.patternHint pat
    case expected of
      Infer {} ->
        inferPat p pat $ \pat' _ patVars argType -> do
          let
            body = instantiatePattern pure (boundPatVars patVars) bodyScope
          (body', bodyType) <- inferRho body (InstUntil Explicit) Nothing
          Context.freshExtend (binding h p argType) $ \argVar -> do
            body'' <- matchSingle (pure argVar) pat' body' bodyType
            logMeta "tc.expr" "Lam Infer bodyType" $ zonk bodyType
            f <- instExpected expected $ Core.pi_ argVar bodyType
            logMeta "tc.expr" "Lam Infer abstracted bodyType" $ zonk $ Core.pi_ argVar bodyType
            return $ f $ Core.lam argVar body''
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let
          h' = h <> typeh
        checkPat p pat mempty argType $ \pat' patExpr patVars -> do
          let
            body = instantiatePattern pure (boundPatVars patVars) bodyScope
            bodyType = Util.instantiate1 patExpr bodyTypeScope
          body' <- checkPoly body bodyType
          Context.freshExtend (binding h' p argType) $ \argVar -> do
            body'' <- matchSingle (pure argVar) pat' body' bodyType
            return $ fResult $ Core.lam argVar body''
  Pre.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstUntil p) expectedAppResult
    (argType, resTypeScope, f1) <- subtypeFun funType p
    let fun'' = f1 fun'
    case unusedScope resTypeScope of
      Nothing -> do
        arg' <- checkPoly arg argType
        let resType = Util.instantiate1 arg' resTypeScope
        f2 <- instExpected expected resType
        return $ f2 $ Core.App fun'' p arg'
      Just resType -> do
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
  :: Vector (SourceLoc, NameHint, Pre.ConstantDef Pre.Expr (Var LetVar FreeVar))
  -> Scope LetVar Pre.Expr FreeVar
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
        set = case a of
          Abstract -> identity
          Concrete -> Context.set var e
      return (var, loc, set)

    body <- foldr ($) identity (thd3 <$> ds')
      $ tcRho (instantiateLet pure vars scope) expected expectedAppResult
    Core.let_ ds' body

tcBranches
  :: PreM
  -> [(Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) (), PatternScope Pre.Expr FreeVar)]
  -> Expected Rhotype
  -> Maybe Rhotype
  -> Elaborate CoreM
tcBranches expr pbrs expected expectedAppResult = do
  (expr', exprType) <- inferRho expr (InstUntil Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) ->
    checkPat Explicit (void pat) mempty exprType $ \pat' _ patVars -> do
      let br = instantiatePattern pure (boundPatVars patVars) brScope
      return (pat', br, patVars)

  case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br, patVars) -> withPatVars patVars $ do
        br' <- checkPoly br resType
        return (pat, br')
      logMeta "tc.branches" "tcBranches check" $ zonk resType
      matchCase expr' brs resType

    Infer _ instUntil -> do
      resType <- existsType mempty
      brs <- forM inferredPats $ \(pat, br, patVars) -> withPatVars patVars $ do
        (br', brType) <- inferRho br instUntil expectedAppResult
        runUnify (unify mempty brType resType) report
        return (pat, br')
      logMeta "tc.branches" "tcBranches infer" $ zonk resType
      f <- instExpected expected resType

      matched <- matchCase expr' brs resType
      return $ f matched
