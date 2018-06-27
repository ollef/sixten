{-# LANGUAGE RecursiveDo #-}
module Inference.TypeCheck.Expr where

import Control.Monad.Except
import Control.Monad.ST
import Data.HashSet(HashSet)
import Data.Monoid
import Data.STRef
import qualified Data.Vector as Vector

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Constraint
import Inference.Constructor
import Inference.Match
import Inference.MetaVar as MetaVar
import Inference.Monad
import Inference.Subtype
import Inference.TypeCheck.Definition
import Inference.TypeCheck.Pattern
import Inference.TypeOf
import Inference.Unify
import MonadContext
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import Util
import VIX

data Expected typ
  = Infer (STRef RealWorld typ) InstUntil
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> Infer (CoreM -> CoreM)
instExpected (Infer r instUntil) t = do
  (t', f) <- instantiateForalls t instUntil
  liftST $ writeSTRef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: PreM -> Polytype -> Infer CoreM
checkPoly expr typ = do
  logPretty 20 "checkPoly expr" $ pretty <$> expr
  logMeta 20 "checkPoly type" typ
  res <- indentLog $ checkPoly' expr typ
  logMeta 20 "checkPoly res expr" res
  return res

checkPoly' :: PreM -> Polytype -> Infer CoreM
checkPoly' (Pre.SourceLoc loc e) polyType
  = located loc $ checkPoly' e polyType
checkPoly' expr@(Pre.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType
  = skolemise polyType (instUntilExpr expr) $ \rhoType f -> do
    e <- checkRho expr rhoType
    return $ f e

instantiateForalls
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, CoreM -> CoreM)
instantiateForalls typ instUntil = do
  typ' <- whnf typ
  instantiateForalls' typ' instUntil

instantiateForalls'
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, CoreM -> CoreM)
instantiateForalls' (Core.Pi h p t s) instUntil
  | shouldInst p instUntil = do
    v <- exists h p t
    let typ = Util.instantiate1 v s
    (result, f) <- instantiateForalls typ instUntil
    return (result, \x -> f $ betaApp x p v)
instantiateForalls' typ _ = return (typ, id)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: PreM -> Rhotype -> Infer CoreM
checkRho expr typ = do
  logPretty 20 "checkRho expr" $ pretty <$> expr
  logMeta 20 "checkRho type" typ
  res <- indentLog $ checkRho' expr typ
  logMeta 20 "checkRho res expr" res
  return res

checkRho' :: PreM -> Rhotype -> Infer CoreM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: PreM -> InstUntil -> Maybe Rhotype -> Infer (CoreM, Rhotype)
inferRho expr instUntil expectedAppResult = do
  logPretty 20 "inferRho" $ pretty <$> expr
  (resExpr, resType) <- indentLog $ inferRho' expr instUntil expectedAppResult
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: PreM -> InstUntil -> Maybe Rhotype -> Infer (CoreM, Rhotype)
inferRho' expr instUntil expectedAppResult = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instUntil) expectedAppResult
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: PreM -> Expected Rhotype -> Maybe Rhotype -> Infer CoreM
tcRho expr expected expectedAppResult = case expr of
  Pre.Var v -> do
    f <- instExpected expected $ varType v
    return $ f $ Core.Var v
  Pre.Global g -> do
    (_, typ) <- definition g
    f <- instExpected expected typ
    return $ f $ Core.Global g
  Pre.Lit l -> do
    f <- instExpected expected $ typeOfLiteral l
    return $ f $ Core.Lit l
  Pre.Con cons -> do
    qc <- resolveConstr cons expectedAppResult
    typ <- qconstructor qc
    f <- instExpected expected typ
    return $ f $ Core.Con qc
  Pre.Pi p pat bodyScope -> do
    (pat', _, patVars, patType) <- inferPat p pat mempty
    withPatVars patVars $ do
      let body = instantiatePattern pure (boundPatVars patVars) bodyScope
          h = Pre.patternHint pat
      body' <- checkPoly body Builtin.Type
      f <- instExpected expected Builtin.Type
      x <- forall h p patType
      body'' <- withVar x $ matchSingle (pure x) pat' body' Builtin.Type
      return $ f $ Core.pi_ x body''
  Pre.Lam p pat bodyScope -> do
    let h = Pre.patternHint pat
    case expected of
      Infer {} -> do
        (pat', _, patVars, argType) <- inferPat p pat mempty
        withPatVars patVars $ do
          let body = instantiatePattern pure (boundPatVars patVars) bodyScope
          (body', bodyType) <- inferRho body (InstUntil Explicit) Nothing
          argVar <- forall h p argType
          body'' <- withVar argVar $ matchSingle (pure argVar) pat' body' bodyType
          f <- instExpected expected $ Core.pi_ argVar bodyType
          return $ f $ Core.lam argVar body''
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let h' = h <> typeh
        (pat', patExpr, patVars) <- checkPat p pat mempty argType
        withPatVars patVars $ do
          let body = instantiatePattern pure (boundPatVars patVars) bodyScope
              bodyType = Util.instantiate1 patExpr bodyTypeScope
          body' <- checkPoly body bodyType
          argVar <- forall h' p argType
          body'' <- withVar argVar $ matchSingle (pure argVar) pat' body' bodyType
          return $ fResult $ Core.lam argVar body''
  Pre.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstUntil p) expectedAppResult
    (argType, resTypeScope, f1) <- subtypeFun funType p
    case unusedScope resTypeScope of
      Nothing -> do
        arg' <- checkPoly arg argType
        let resType = Util.instantiate1 arg' resTypeScope
        f2 <- instExpected expected resType
        let fun'' = f1 fun'
        return $ f2 $ Core.App fun'' p arg'
      Just resType -> do
        f2 <- instExpected expected resType
        arg' <- checkPoly arg argType
        let fun'' = f1 fun'
        return $ f2 $ Core.App fun'' p arg'
  Pre.Let ds scope -> enterLevel $ do
    evars <- forM ds $ \(_, name, _) -> do
      typ <- existsType name
      forall name Explicit typ
    let instantiatedDs
          = (\(loc, _, def) ->
              ( loc
              , Pre.ConstantDefinition $ Pre.instantiateLetConstantDef pure evars def
              )) <$> ds
    ds' <- checkAndGeneraliseDefs False (Vector.zip evars instantiatedDs)
    let evars' = fst <$> ds'
        eabstr = letAbstraction evars'
    let ds'' = LetRec
          $ flip fmap ds'
          $ \(v, ConstantDefinition _ _ e) -> LetBinding (varHint v) (abstract eabstr e) $ varType v
    mdo
      let inst = instantiateLet pure vars
      vars <- iforMLet ds'' $ \i h s t -> do
        let (_, ConstantDefinition a _ _) = ds' Vector.! i
        case a of
          Abstract -> forall h Explicit t
          Concrete -> letVar h Explicit (inst s) t
      let abstr = letAbstraction vars
      body <- withVars vars $ tcRho (instantiateLet pure vars scope) expected expectedAppResult
      return $ Core.Let ds'' $ abstract abstr body
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
  Pre.SourceLoc loc e -> located loc $ tcRho e expected expectedAppResult

tcBranches
  :: PreM
  -> [(Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) (), PatternScope Pre.Expr FreeV)]
  -> Expected Rhotype
  -> Maybe Rhotype
  -> Infer CoreM
tcBranches expr pbrs expected expectedAppResult = do
  (expr', exprType) <- inferRho expr (InstUntil Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) -> do
    (pat', _, patVars) <- checkPat Explicit (void pat) mempty exprType
    let br = instantiatePattern pure (boundPatVars patVars) brScope
    return (pat', br, patVars)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br, patVars) -> withPatVars patVars $ do
        br' <- checkRho br resType
        return (pat, br')
      return (brs, resType)
    Infer _ instUntil -> do
      resType <- existsType mempty
      brs <- forM inferredPats $ \(pat, br, patVars) -> withPatVars patVars $ do
        (br', brType) <- inferRho br instUntil expectedAppResult
        unify mempty brType resType
        return (pat, br')
      return (brs, resType)

  f <- instExpected expected resType

  matched <- matchCase expr' inferredBranches resType
  return $ f matched
