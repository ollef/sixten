{-# LANGUAGE FlexibleContexts, OverloadedStrings, RecursiveDo #-}
module Inference.TypeCheck where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import Data.STRef
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Analysis.Simplify
import qualified Builtin.Names as Builtin
import Inference.Class as Class
import Inference.Clause
import Inference.Cycle
import Inference.Match as Match
import Inference.Monad
import Inference.Normalise
import Inference.Subtype
import Inference.TypeOf
import Inference.Unify
import Meta
import Syntax
import qualified Syntax.Abstract as Abstract
import Syntax.Abstract.Pattern as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import qualified TypeRep
import Util
import Util.TopoSort
import VIX

data Expected typ
  = Infer (STRef RealWorld typ) InstUntil
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> Infer (AbstractM -> Infer AbstractM)
instExpected (Infer r instUntil) t = do
  (t', f) <- instantiateForalls t instUntil
  liftST $ writeSTRef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: ConcreteM -> Polytype -> Infer AbstractM
checkPoly expr typ = do
  logMeta 20 "checkPoly expr" expr
  logMeta 20 "checkPoly type" typ
  modifyIndent succ
  res <- checkPoly' expr typ
  modifyIndent pred
  logMeta 20 "checkPoly res expr" res
  return res

checkPoly' :: ConcreteM -> Polytype -> Infer AbstractM
checkPoly' expr@(Concrete.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType = do
  (vs, rhoType, f) <- prenexConvert polyType $ instUntilExpr expr
  e <- checkRho expr rhoType
  logShow 25 "checkPoly: prenexConvert vars" vs
  f =<< Abstract.lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) e

instUntilExpr :: Concrete.Expr v -> InstUntil
instUntilExpr (Concrete.Lam p _ _) = InstUntil p
instUntilExpr _ = InstUntil Explicit

-- inferPoly :: ConcreteM -> InstUntil -> Infer (AbstractM, Polytype)
-- inferPoly expr instUntil = do
--   logMeta 20 "inferPoly expr" expr
--   modifyIndent succ
--   (resExpr, resType) <- inferPoly' expr instUntil
--   modifyIndent pred
--   logMeta 20 "inferPoly res expr" resExpr
--   logMeta 20 "inferPoly res typ" resType
--   return (resExpr, resType)

-- inferPoly' :: ConcreteM -> InstUntil -> Infer (AbstractM, Polytype)
-- inferPoly' expr instUntil = do
--   (expr', exprType) <- inferRho expr instUntil
--   generalise expr' exprType

instantiateForalls
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
instantiateForalls typ instUntil = do
  typ' <- whnf typ
  instantiateForalls' typ' instUntil

instantiateForalls'
  :: Polytype
  -> InstUntil
  -> Infer (Rhotype, AbstractM -> Infer AbstractM)
instantiateForalls' (Abstract.Pi h p t s) instUntil
  | shouldInst p instUntil = do
    v <- existsVar h p t
    let typ = Util.instantiate1 v s
    (result, f) <- instantiateForalls typ instUntil
    return (result, \x -> f $ betaApp x p v)
instantiateForalls' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: ConcreteM -> Rhotype -> Infer AbstractM
checkRho expr typ = do
  logMeta 20 "checkRho expr" expr
  logMeta 20 "checkRho type" typ
  modifyIndent succ
  res <- checkRho' expr typ
  modifyIndent pred
  logMeta 20 "checkRho res expr" res
  return res

checkRho' :: ConcreteM -> Rhotype -> Infer AbstractM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: ConcreteM -> InstUntil -> Maybe Rhotype -> Infer (AbstractM, Rhotype)
inferRho expr instUntil expectedAppResult = do
  logMeta 20 "inferRho" expr
  modifyIndent succ
  (resExpr, resType) <- inferRho' expr instUntil expectedAppResult
  modifyIndent pred
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: ConcreteM -> InstUntil -> Maybe Rhotype -> Infer (AbstractM, Rhotype)
inferRho' expr instUntil expectedAppResult = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instUntil) expectedAppResult
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: ConcreteM -> Expected Rhotype -> Maybe Rhotype -> Infer AbstractM
tcRho expr expected expectedAppResult = case expr of
  Concrete.Var v -> do
    f <- instExpected expected $ metaType v
    f $ Abstract.Var v
  Concrete.Global g -> do
    (_, typ) <- definition g
    f <- instExpected expected typ
    f $ Abstract.Global g
  Concrete.Lit l -> do
    f <- instExpected expected $ typeOfLiteral l
    f $ Abstract.Lit l
  Concrete.Con cons -> do
    qc <- resolveConstr cons expectedAppResult
    typ <- qconstructor qc
    f <- instExpected expected typ
    f $ Abstract.Con qc
  Concrete.Pi p pat bodyScope -> do
    (pat', _, vs, patType) <- inferPat p pat mempty
    let body = instantiatePattern pure vs bodyScope
        h = Concrete.patternHint pat
    body' <- enterLevel $ checkPoly body Builtin.Type
    f <- instExpected expected Builtin.Type
    x <- forall h p patType
    body'' <- matchSingle (pure x) pat' body' Builtin.Type
    f =<< Abstract.Pi h p patType <$> abstract1M x body''
  Concrete.Lam p pat bodyScope -> do
    let h = Concrete.patternHint pat
    case expected of
      Infer {} -> do
        (pat', _, vs, argType) <- inferPat p pat mempty
        let body = instantiatePattern pure vs bodyScope
        (body', bodyType) <- enterLevel $ inferRho body (InstUntil Explicit) Nothing
        argVar <- forall h p argType
        body'' <- matchSingle (pure argVar) pat' body' bodyType
        bodyScope' <- abstract1M argVar body''
        bodyTypeScope <- abstract1M argVar bodyType
        f <- instExpected expected $ Abstract.Pi h p argType bodyTypeScope
        f $ Abstract.Lam h p argType bodyScope'
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let h' = h <> typeh
        (pat', patExpr, vs) <- checkPat p pat mempty argType
        let body = instantiatePattern pure vs bodyScope
            bodyType = Util.instantiate1 patExpr bodyTypeScope
        body' <- enterLevel $ checkPoly body bodyType
        argVar <- forall h' p argType
        body'' <- matchSingle (pure argVar) pat' body' bodyType
        fResult =<< Abstract.Lam h' p argType <$> abstract1M argVar body''
  Concrete.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstUntil p) expectedAppResult
    (argType, resTypeScope, f1) <- subtypeFun funType p
    case unusedScope resTypeScope of
      Nothing -> do
        arg' <- checkPoly arg argType
        let resType = Util.instantiate1 arg' resTypeScope
        f2 <- instExpected expected resType
        fun'' <- f1 fun'
        f2 $ Abstract.App fun'' p arg'
      Just resType -> do
        f2 <- instExpected expected resType
        arg' <- checkPoly arg argType
        fun'' <- f1 fun'
        f2 $ Abstract.App fun'' p arg'
  Concrete.Let ds scope -> enterLevel $ do
    let names = (\(_, n, _, _) -> n) <$> ds
    evars <- forM names $ \name -> do
      typ <- existsType name
      forall name Explicit typ
    let instantiatedDs
          = (\(loc, _, def, typ) ->
              ( loc
              , Concrete.TopLevelPatDefinition $ Concrete.instantiateLetClause pure evars <$> def
              , instantiateLet pure evars typ
              )) <$> ds
    ds' <- checkRecursiveDefs False (Vector.zip evars instantiatedDs)
    let eabstr = letAbstraction evars
    ds'' <- LetRec
      <$> forM ds'
        (\(v, Definition _ _ e, t) -> LetBinding (metaHint v) <$> abstractM eabstr e <*> pure t)
    mdo
      let inst = instantiateLet pure vars
      vars <- iforMLet ds'' $ \i h s t -> do
        let (_, Definition a _ _, _) = ds' Vector.! i
        case a of
          Abstract -> forall h Explicit t
          Concrete -> Meta.let_ h Explicit (inst s) t
      let abstr = letAbstraction vars
      body <- tcRho (instantiateLet pure vars scope) expected expectedAppResult
      Abstract.Let ds'' <$> abstractM abstr body
  Concrete.Case e brs -> tcBranches e brs expected
  Concrete.ExternCode c -> do
    c' <- mapM (\e -> fst <$> inferRho e (InstUntil Explicit) Nothing) c
    returnType <- existsType mempty
    f <- instExpected expected returnType
    f $ Abstract.ExternCode c' returnType
  Concrete.Wildcard -> do
    t <- existsType mempty
    f <- instExpected expected t
    x <- existsVar mempty Explicit t
    f x
  Concrete.SourceLoc loc e -> located loc $ tcRho e expected expectedAppResult

tcBranches
  :: ConcreteM
  -> [(Concrete.Pat (PatternScope Concrete.Expr MetaA) (), PatternScope Concrete.Expr MetaA)]
  -> Expected Rhotype
  -> Infer AbstractM
tcBranches expr pbrs expected = do
  (expr', exprType) <- inferRho expr (InstUntil Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) -> do
    (pat', _, vs) <- checkPat Explicit (void pat) mempty exprType
    let br = instantiatePattern pure vs brScope
    return (pat', br)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br) -> do
        br' <- checkRho br resType
        return (pat, br')
      return (brs, resType)
    Infer _ instUntil -> case inferredPats of
      [] -> do
        resType <- existsType mempty
        return ([], resType)
      (headPat, headBr):inferredPats' -> do
        (headBr', resType) <- inferRho headBr instUntil Nothing
        brs' <- forM inferredPats' $ \(pat, br) -> do
          br' <- checkRho br resType
          return (pat, br')
        return ((headPat, headBr') : brs', resType)

  f <- instExpected expected resType

  matched <- matchCase expr' inferredBranches resType
  f matched

--------------------------------------------------------------------------------
-- Patterns
data ExpectedPat
  = InferPat (STRef RealWorld AbstractM)
  | CheckPat AbstractM

checkPat
  :: Plicitness
  -> Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> Polytype
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
checkPat p pat vs expectedType = tcPat p pat vs $ CheckPat expectedType

inferPat
  :: Plicitness
  -> Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA, Polytype)
inferPat p pat vs = do
  ref <- liftST $ newSTRef $ error "inferPat: empty result"
  (pat', patExpr, vs') <- tcPat p pat vs $ InferPat ref
  t <- liftST $ readSTRef ref
  return (pat', patExpr, vs', t)

tcPats
  :: Vector (Plicitness, Concrete.Pat (PatternScope Concrete.Expr MetaA) ())
  -> Vector MetaA
  -> Telescope Plicitness Abstract.Expr MetaA
  -> Infer (Vector (Abstract.Pat AbstractM MetaA, AbstractM, AbstractM), Vector MetaA)
tcPats pats vs tele = do
  unless (Vector.length pats == teleLength tele)
    $ throwError "tcPats length mismatch"
  results <- iforTeleWithPrefixM tele $ \i _ _ s prefix -> do
    let argExprs = snd3 . fst <$> prefix
        vs' | Vector.null prefix = vs
            | otherwise = snd $ Vector.last prefix
        expectedType = instantiateTele id argExprs s
        (p, pat) = pats Vector.! i
    (pat', patExpr, vs'') <- checkPat p pat vs' expectedType
    return ((pat', patExpr, expectedType), vs'')

  let vs' | Vector.null results = vs
          | otherwise = snd $ Vector.last results
  return (fst <$> results, vs')

tcPat
  :: Plicitness
  -> Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> ExpectedPat
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
tcPat p pat vs expected = do
  whenVerbose 20 $ do
    shownPat <- bitraverse (showMeta . instantiatePattern pure vs) pure pat
    logPretty 20 "tcPat" shownPat
  logMeta 30 "tcPat vs" vs
  modifyIndent succ
  (pat', patExpr, vs') <- tcPat' p pat vs expected
  modifyIndent pred
  logMeta 20 "tcPat res" =<< bitraverse showMeta pure pat'
  logMeta 30 "tcPat vs res" vs'
  return (pat', patExpr, vs')

tcPat'
  :: Plicitness
  -> Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> ExpectedPat
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
tcPat' p pat vs expected = case pat of
  Concrete.VarPat h () -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType h
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall h p expectedType
    return (Abstract.VarPat h v, pure v, vs <> pure v)
  Concrete.WildcardPat -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType mempty
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall mempty p expectedType
    return (Abstract.VarPat mempty v, pure v, vs)
  Concrete.LitPat lit -> do
    (pat', expr) <- instPatExpected
      expected
      (typeOfLiteral lit)
      (LitPat lit)
      (Abstract.Lit lit)
    return (pat', expr, vs)
  Concrete.ConPat cons pats -> do
    qc@(QConstr typeName _) <- resolveConstr cons $ case expected of
      CheckPat expectedType -> Just expectedType
      InferPat _ -> Nothing
    (_, typeType) <- definition typeName
    conType <- qconstructor qc

    let paramsTele = Abstract.telescope typeType
        numParams = teleLength paramsTele
        (tele, retScope) = Abstract.pisView conType
        argPlics = Vector.drop numParams $ teleAnnotations tele

    pats' <- Vector.fromList <$> exactlyEqualisePats (Vector.toList argPlics) (Vector.toList pats)

    paramVars <- forTeleWithPrefixM paramsTele $ \h p' s paramVars ->
      existsVar h p' $ instantiateTele id paramVars s

    let argTele = instantiatePrefix paramVars tele

    (pats'', vs') <- tcPats pats' vs argTele

    let argExprs = snd3 <$> pats''
        argTypes = thd3 <$> pats''
        pats''' = Vector.zip3 argPlics (fst3 <$> pats'') argTypes
        params = Vector.zip (teleAnnotations paramsTele) paramVars
        iparams = first implicitise <$> params
        patExpr = Abstract.apps (Abstract.Con qc) $ iparams <> Vector.zip argPlics argExprs

        retType = instantiateTele id (paramVars <|> argExprs) retScope

    (pat', patExpr') <- instPatExpected expected retType (Abstract.ConPat qc params pats''') patExpr

    return (pat', patExpr', vs')
  Concrete.AnnoPat s pat' -> do
    let patType = instantiatePattern pure vs s
    patType' <- checkPoly patType Builtin.Type
    (pat'', patExpr, vs') <- checkPat p pat' vs patType'
    (pat''', patExpr') <- instPatExpected expected patType' pat'' patExpr
    return (pat''', patExpr', vs')
  Concrete.ViewPat _ _ -> throwError "tcPat ViewPat undefined TODO"
  Concrete.PatLoc loc pat' -> located loc $ tcPat' p pat' vs expected

instPatExpected
  :: ExpectedPat
  -> Polytype -- ^ patType
  -> Abstract.Pat AbstractM MetaA -- ^ pat
  -> AbstractM -- ^ :: patType
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM) -- ^ (pat :: expectedType, :: expectedType)
instPatExpected (CheckPat expectedType) patType pat patExpr = do
  f <- subtype expectedType patType
  viewPat expectedType pat patExpr f
instPatExpected (InferPat ref) patType pat patExpr = do
  liftST $ writeSTRef ref patType
  return (pat, patExpr)

viewPat
  :: AbstractM -- ^ expectedType
  -> Abstract.Pat AbstractM MetaA -- ^ pat
  -> AbstractM -- ^ :: patType
  -> (AbstractM -> Infer AbstractM) -- ^ expectedType -> patType
  -> Infer (Abstract.Pat AbstractM MetaA, AbstractM) -- ^ (expectedType, :: expectedType)
viewPat expectedType pat patExpr f = do
  x <- forall mempty Explicit expectedType
  fx <- f $ pure x
  if fx == pure x then
    return (pat, patExpr)
  else do
    fExpr <- Abstract.Lam mempty Explicit expectedType <$> abstract1M x fx
    return (Abstract.ViewPat fExpr pat, pure x)

patToTerm
  :: Abstract.Pat AbstractM MetaA
  -> Infer (Maybe AbstractM)
patToTerm pat = case pat of
  Abstract.VarPat _ v -> return $ Just $ Abstract.Var v
  Abstract.ConPat qc params pats -> do
    mterms <- mapM (\(p, pat', _typ') -> fmap ((,) p) <$> patToTerm pat') pats
    case sequence mterms of
      Nothing -> return Nothing
      Just terms -> return $ Just $
        Abstract.apps (Abstract.Con qc) $ params <> terms
  Abstract.LitPat l -> return $ Just $ Abstract.Lit l
  Abstract.ViewPat{} -> return Nothing

{-
instantiateDataType
  :: Applicative f
  => Name
  -> Infer (AbstractM, Vector (Plicitness, f MetaA))
instantiateDataType typeName = mdo
  (_, dataTypeType) <- definition typeName
  let params = telescope dataTypeType
      inst = instantiateTele (pure . snd) paramVars
  paramVars <- forMTele params $ \h p s -> do
    v <- exists h p (inst s)
    return (p, v)
  let pureParamVars = fmap pure <$> paramVars
      dataType = Abstract.apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(p, v) -> (implicitise, pure v)) <$> paramVars
  return (dataType, implicitParamVars)
-}

--------------------------------------------------------------------------------
-- Constrs
resolveConstr
  :: HashSet QConstr
  -> Maybe Rhotype
  -> Infer QConstr
resolveConstr cs expected = do
  mExpectedTypeName <- expectedDataType

  when (HashSet.null cs) $
    err
      "No such data type"
      ["There is no data type with the" Leijen.<+> constrDoc <> "."]

  let candidates
        = maybe
          cs
          (\e -> HashSet.filter ((== e) . qconstrTypeName) cs)
          mExpectedTypeName

  case (HashSet.toList candidates, mExpectedTypeName) of
    ([], Just expectedTypeName) ->
      err "Undefined constructor"
        [ Leijen.dullgreen (pretty expectedTypeName)
        Leijen.<+> "doesn't define the"
        Leijen.<+> constrDoc <> "."
        ]
    ([x], _) -> return x
    (xs, _) -> err "Ambiguous constructor"
      [ "Unable to infer the type for the" Leijen.<+> constrDoc <> "."
      , "Possible data types:"
      Leijen.<+> prettyHumanList "or" (Leijen.dullgreen . pretty <$> xs)
      <> "."
      ]
  where
    expectedDataType = join <$> traverse findExpectedDataType expected
    findExpectedDataType :: AbstractM -> Infer (Maybe QName)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h p t s -> do
          v <- forall h p t
          findExpectedDataType $ Util.instantiate1 (pure v) s
        Abstract.App t1 _ _ -> findExpectedDataType t1
        Abstract.Global v -> do
          (d, _) <- definition v
          return $ case d of
            DataDefinition _ _ -> Just v
            _ -> Nothing
        _ -> return Nothing
    err heading docs = do
      loc <- currentLocation
      throwError
        $ show
        $ explain loc
        $ Err (Just heading) docs mempty mempty
    constrDoc = case (Leijen.red . pretty) <$> HashSet.toList cs of
      [pc] -> "constructor" Leijen.<+> pc
      pcs -> "constructors" Leijen.<+> prettyHumanList "and" pcs

--------------------------------------------------------------------------------
-- Generalisation
{-
generalise
  :: AbstractM
  -> AbstractM
  -> Infer (AbstractM, AbstractM)
generalise expr typ = do
  -- fvs <- (<>) <$> foldMapM (:[]) typ' <*> foldMapM (:[]) expr
  fvs <- foldMapM (:[]) typ -- <*> foldMapM (:[]) expr'
  l <- level
  let p v@MetaVar { metaRef = Just r } = either (>= l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HashSet.fromList <$> filterM p fvs

  deps <- forM (HashSet.toList fvs') $ \x -> do
    ds <- foldMapM HashSet.singleton $ metaType x
    return (x, ds)

  let sorted = map go $ topoSort deps
      isorted = (,) Implicit <$> sorted
  genexpr <- abstractMs isorted Abstract.Lam expr
  gentype <- abstractMs isorted Abstract.Pi typ

  return (genexpr, gentype)
  where
    go [v] = v
    go _ = error "Generalise"
    -}

--------------------------------------------------------------------------------
-- Definitions
checkConstrDef
  :: ConstrDef ConcreteM
  -> Infer (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c typ) = do
  typ' <- zonk =<< checkPoly typ Builtin.Type
  (sizes, ret) <- go typ'
  let size = foldl' productType (Abstract.MkType TypeRep.UnitRep) sizes
  return (ConstrDef c typ', ret, size)
  where
    go :: AbstractM -> Infer ([AbstractM], AbstractM)
    go (Abstract.Pi h p t s) = do
      v <- forall h p t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      return (t : sizes, ret)
    go ret = return ([], ret)

checkDataType
  :: MetaA
  -> DataDef Concrete.Expr MetaA
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkDataType name (DataDef cs) typ = do
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  ps' <- forTeleWithPrefixM (Abstract.telescope typ') $ \h p s ps' -> do
    let is = instantiateTele pure (snd <$> ps') s
    v <- forall h p is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = Abstract.apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

  mapM_ (unify [] constrRetType) rets

  intRep <- gets $ TypeRep.intRep . vixTarget

  let tagRep = case cs of
        [] -> TypeRep.UnitRep
        [_] -> TypeRep.UnitRep
        _ -> intRep

      typeRep
        = productType (Abstract.MkType tagRep)
        $ foldl' sumType (Abstract.MkType TypeRep.UnitRep) sizes

  unify [] Builtin.Type =<< typeOfM constrRetType

  abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
    logMeta 20 ("checkDataType res " ++ show qc) e
    traverse (abstractM abstr) c

  params <- metaTelescopeM ps'
  let typ'' = Abstract.pis params $ Scope Builtin.Type

  typeRep' <- whnf' True typeRep
  abstractedTypeRep <- abstractM abstr typeRep'
  logMeta 20 "checkDataType typeRep" typeRep'

  return (DataDefinition (DataDef abstractedCs) $ Abstract.lams params abstractedTypeRep, typ'')

checkClauses
  :: NonEmpty (Concrete.Clause Void Concrete.Expr MetaA)
  -> Polytype
  -> Infer AbstractM
checkClauses clauses polyType = do
  forM_ clauses $ logMeta 20 "checkClauses clause"
  logMeta 20 "checkClauses typ" polyType

  modifyIndent succ

  (vs, rhoType, f) <- prenexConvert polyType $ minimum $ instUntilClause <$> clauses

  ps <- piPlicitnesses rhoType

  clauses' <- forM clauses $ \(Concrete.Clause pats body) -> do
    pats' <- equalisePats ps $ Vector.toList pats
    return $ Concrete.Clause (Vector.fromList pats') body

  let equalisedClauses = equaliseClauses clauses'

  forM_ equalisedClauses $ logMeta 20 "checkClauses equalisedClause"

  res <- checkClausesRho equalisedClauses rhoType

  modifyIndent pred
  l <- level
  logMeta 20 ("checkClauses res " <> show l) res

  f =<< Abstract.lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) res
  where
    instUntilClause :: Concrete.Clause Void Concrete.Expr v -> InstUntil
    instUntilClause (Concrete.Clause pats s)
      | Vector.length pats > 0 = InstUntil $ fst $ Vector.head pats
      | otherwise = instUntilExpr $ fromScope s

    piPlicitnesses :: AbstractM -> Infer [Plicitness]
    piPlicitnesses t = do
      t' <- whnf t
      piPlicitnesses' t'

    piPlicitnesses' :: AbstractM -> Infer [Plicitness]
    piPlicitnesses' (Abstract.Pi h p t s) = do
      v <- forall h p t
      (:) p <$> piPlicitnesses (instantiate1 (pure v) s)
    piPlicitnesses' _ = return mempty

checkClausesRho
  :: NonEmpty (Concrete.Clause Void Concrete.Expr MetaA)
  -> Rhotype
  -> Infer AbstractM
checkClausesRho clauses rhoType = do
  forM_ clauses $ logMeta 20 "checkClausesRho clause"
  logMeta 20 "checkClausesRho type" rhoType

  let (ps, firstPats) = Vector.unzip ppats
        where
          Concrete.Clause ppats _ = NonEmpty.head clauses
  (argTele, returnTypeScope, fs) <- funSubtypes rhoType ps

  modifyIndent succ

  clauses' <- forM clauses $ \clause -> do
    let pats = Concrete.clausePatterns' clause
        bodyScope = Concrete.clauseScope' clause
    (pats', patVars) <- tcPats pats mempty argTele
    let body = instantiatePattern pure patVars bodyScope
        argExprs = snd3 <$> pats'
        returnType = instantiateTele id argExprs returnTypeScope
    body' <- checkRho body returnType
    return (fst3 <$> pats', body')

  modifyIndent pred

  forM_ clauses' $ \(pats, body) -> do
    forM_ pats $ logMeta 20 "checkClausesRho clause pat" <=< bitraverse showMeta pure
    logMeta 20 "checkClausesRho clause body" body

  argVars <- forTeleWithPrefixM (addTeleNames argTele $ Concrete.patternHint <$> firstPats) $ \h p s argVars ->
    forall h p $ instantiateTele pure argVars s

  let returnType = instantiateTele pure argVars returnTypeScope

  body <- matchClauses
    (Vector.toList $ pure <$> argVars)
    (NonEmpty.toList $ first Vector.toList <$> clauses')
    returnType

  logMeta 25 "checkClausesRho body res" body

  result <- foldrM
    (\(p, (f, v)) e ->
      f =<< Abstract.Lam (metaHint v) p (metaType v) <$> abstract1M v e)
    body
    (Vector.zip ps $ Vector.zip fs argVars)

  logMeta 20 "checkClausesRho res" result
  return result

checkDefType
  :: Concrete.PatDefinition (Concrete.Clause Void Concrete.Expr MetaA)
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkDefType (Concrete.PatDefinition a i clauses) typ = do
  e' <- checkClauses clauses typ
  return (Definition a i e', typ)

checkTopLevelDefType
  :: MetaA
  -> Concrete.TopLevelPatDefinition Concrete.Expr MetaA
  -> SourceLoc
  -> AbstractM
  -> Infer (Definition Abstract.Expr MetaA, AbstractM)
checkTopLevelDefType v def loc typ = located (render loc) $ case def of
  Concrete.TopLevelPatDefinition def' -> checkDefType def' typ
  Concrete.TopLevelPatDataDefinition d -> checkDataType v d typ
  -- Should be removed by Declassify:
  Concrete.TopLevelPatClassDefinition _ -> error "checkTopLevelDefType class"
  Concrete.TopLevelPatInstanceDefinition _ -> error "checkTopLevelDefType instance"

generaliseDef
  :: Vector MetaA
  -> Definition Abstract.Expr MetaA
  -> AbstractM
  -> Infer ( Definition Abstract.Expr MetaA
         , AbstractM
         )
generaliseDef vs (Definition a i e) t = do
  let ivs = (\v -> (implicitise $ metaData v, v)) <$> vs
  ge <- abstractMs ivs Abstract.Lam e
  gt <- abstractMs ivs Abstract.Pi t
  return (Definition a i ge, gt)
generaliseDef vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
      ivs = (\v -> (implicitise $ metaData v, v)) <$> vs
  -- Abstract vs on top of typ
  grep <- abstractMs ivs Abstract.Lam rep
  gtyp <- abstractMs ivs Abstract.Pi typ
  return (DataDefinition (DataDef cs') grep, gtyp)
  where
    varIndex = hashedElemIndex vs
    f v = pure $ maybe (F v) (B . TeleVar) (varIndex v)
    g = pure . B . (+ TeleVar (length vs))

abstractMs
  :: Foldable t
  => t (Plicitness, MetaA)
  -> (NameHint -> Plicitness -> AbstractM -> ScopeM () Abstract.Expr -> AbstractM)
  -> AbstractM
  -> Infer AbstractM
abstractMs vs c b = foldrM
  (\(p, v)  s -> c (metaHint v) p (metaType v) <$> abstract1M v s)
  b
  vs

generaliseDefs
  :: Vector
    ( MetaA
    , Definition Abstract.Expr MetaA
    , AbstractM
    )
  -> Infer
    ( Vector
      ( MetaA
      , Definition Abstract.Expr MetaA
      , AbstractM
      )
    )
generaliseDefs xs = do
  modifyIndent succ

  let vars  = (\(v, _, _) -> v) <$> xs
      varIndex = hashedElemIndex vars
      defs = (\(_, d, _) -> d) <$> xs
      types = (\(_, _, t) -> t) <$> xs

  dfvs <- fold <$> mapM (foldMapM HashSet.singleton) defs
  tfvs <- fold <$> mapM (foldMapM HashSet.singleton) types
  let fvs = dfvs <> tfvs

  mergeConstraintVars fvs

  l <- level
  logShow 30 "level" l
  let p MetaVar { metaRef = Exists r } = either (>= l) (const False) <$> solution r
      p MetaVar { metaRef = Forall } = return False
      p MetaVar { metaRef = LetRef {} } = return False
  fvs' <- fmap HashSet.fromList $ filterM p $ HashSet.toList fvs

  deps <- forM (HashSet.toList fvs') $ \x -> do
    ds <- foldMapM HashSet.singleton $ metaType x
    return (x, ds)

  let sortedFvs = map acyclic $ topoSort deps
      sortedFvsVec = Vector.fromList sortedFvs
      appl x = Abstract.apps x [(implicitise $ metaData fv, pure fv) | fv <- sortedFvs]
      instVars = appl . pure <$> vars
      sub v = fromMaybe (pure v) $ (instVars Vector.!?) =<< varIndex v

  instDefs <- forM xs $ \(v, d, t) -> do
    d' <- boundM (return . sub) d
    t' <- bindM (return . sub) t
    return (v, d', t')

  genDefs <- forM instDefs $ \(v, d, t) -> do
    (d', t') <- generaliseDef sortedFvsVec d t
    return (v, d', t')

  modifyIndent pred

  return genDefs
  where
    acyclic (AcyclicSCC a) = a
    acyclic (CyclicSCC _) = error "generaliseDefs"

implicitise :: Plicitness -> Plicitness
implicitise Constraint = Constraint
implicitise Implicit = Implicit
implicitise Explicit = Implicit

checkRecursiveDefs
  :: Bool
  -> Vector
    ( MetaA
    , ( SourceLoc
      , Concrete.TopLevelPatDefinition Concrete.Expr MetaA
      , ConcreteM
      )
    )
  -> Infer
    (Vector
      ( MetaA
      , Definition Abstract.Expr MetaA
      , AbstractM
      )
    )
checkRecursiveDefs forceGeneralisation defs = do
  let localInstances
        = flip Vector.mapMaybe defs
        $ \(v, (_, def, _)) -> case def of
          Concrete.TopLevelPatDefinition (Concrete.PatDefinition _ IsInstance _) -> Just v { metaData = Constraint }
          _ -> Nothing
  withVars localInstances $ do
    forM_ defs $ \(evar, (_, _, typ)) -> do
      typ' <- checkPoly typ Builtin.Type
      unify [] (metaType evar) typ'

    checkedDefs <- forM defs $ \(evar, (loc, def, _)) -> do
      (def', typ'') <- checkTopLevelDefType evar def loc $ metaType evar
      logMeta 20 ("checkRecursiveDefs res " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) def'
      logMeta 20 ("checkRecursiveDefs res t " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) typ''
      return (loc, (evar, def', typ''))

    detectTypeRepCycles checkedDefs
    detectDefCycles checkedDefs

    elabDefs <- elabRecursiveDefs $ snd <$> checkedDefs

    shouldGen <- if forceGeneralisation then return True else shouldGeneralise elabDefs
    if shouldGen then
      generaliseDefs elabDefs
    else
      return elabDefs

shouldGeneralise
  :: Vector
    ( MetaA
    , Definition Abstract.Expr MetaA
    , AbstractM
    )
  -> Infer Bool
shouldGeneralise defs
  = and
  <$> mapM (\(_, def, _) -> shouldGeneraliseDef def) defs
  where
    shouldGeneraliseDef (Definition _ _ e) = startsWithLambda <$> semiZonk e
    shouldGeneraliseDef DataDefinition {} = return True
    startsWithLambda Abstract.Lam {} = True
    startsWithLambda _ = False

checkTopLevelRecursiveDefs
  :: Vector
    ( QName
    , SourceLoc
    , Concrete.TopLevelPatDefinition Concrete.Expr Void
    , Concrete.Type Void
    )
  -> Infer
    (Vector
      ( QName
      , Definition Abstract.Expr Void
      , Abstract.Type Void
      )
    )
checkTopLevelRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  (checkedDefs, evars) <- enterLevel $ do
    evars <- forM names $ \name -> do
      let hint = fromQName name
      typ <- existsType hint
      forall hint Explicit typ

    let nameIndex = hashedElemIndex names
        expose name = case nameIndex name of
          Nothing -> global name
          Just index -> pure
            $ fromMaybe (error "checkTopLevelRecursiveDefs 1")
            $ evars Vector.!? index

    let exposedDefs = flip fmap defs $ \(_, loc, def, typ) ->
          (loc, bound absurd expose def, bind absurd expose typ)

    checkedDefs <- checkRecursiveDefs True (Vector.zip evars exposedDefs)

    return (checkedDefs, evars)

  let varIndex = hashedElemIndex evars
      unexpose evar = case varIndex evar of
        Nothing -> pure evar
        Just index -> global
          $ fromMaybe (error "checkTopLevelRecursiveDefs 2")
          $ names Vector.!? index
      vf :: MetaA -> Infer b
      vf v = throwError $ "checkTopLevelRecursiveDefs " ++ show v

  forM (Vector.zip names checkedDefs) $ \(name, (_, def, typ)) -> do
    unexposedDef <- boundM (pure . unexpose) def
    unexposedTyp <- bindM (pure . unexpose) typ
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedDef " ++ show (pretty name)) unexposedDef
    logMeta 20 ("checkTopLevelRecursiveDefs unexposedTyp " ++ show (pretty name)) unexposedTyp
    unexposedDef' <- traverse vf unexposedDef
    unexposedTyp' <- traverse vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')

-------------------------------------------------------------------------------
-- Type helpers
productType :: Abstract.Expr v -> Abstract.Expr v -> Abstract.Expr v
productType (Abstract.MkType TypeRep.UnitRep) e = e
productType e (Abstract.MkType TypeRep.UnitRep) = e
productType (Abstract.MkType a) (Abstract.MkType b) = Abstract.MkType $ TypeRep.product a b
productType a b = Builtin.ProductTypeRep a b

sumType :: Abstract.Expr v -> Abstract.Expr v -> Abstract.Expr v
sumType (Abstract.MkType TypeRep.UnitRep) e = e
sumType e (Abstract.MkType TypeRep.UnitRep) = e
sumType (Abstract.MkType a) (Abstract.MkType b) = Abstract.MkType $ TypeRep.sum a b
sumType a b = Builtin.SumTypeRep a b
