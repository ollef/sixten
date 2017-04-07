{-# LANGUAGE OverloadedStrings, TypeFamilies, ViewPatterns #-}
module Inference.TypeCheck where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.ST()
import Control.Monad.ST.Class
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import qualified Data.HashSet as HashSet
import Data.List as List
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import Data.STRef
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Analysis.Simplify
import qualified Backend.Target as Target
import qualified Builtin
import Inference.Clause
import Inference.Cycle
import Inference.Match as Match
import Inference.Normalise
import Inference.TypeOf
import Inference.Unify
import Meta
import Syntax
import qualified Syntax.Abstract as Abstract
import Syntax.Abstract.Pattern as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TopoSort
import Util
import VIX

type Polytype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

newtype InstBelow = InstBelow Plicitness
  deriving (Eq, Ord)

data Expected typ
  = Infer (STRef (World VIX) typ) InstBelow
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> VIX (AbstractM -> VIX AbstractM)
instExpected (Infer r instBelow) t = do
  (t', f) <- instantiateForalls t instBelow
  liftST $ writeSTRef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: ConcreteM -> Polytype -> VIX AbstractM
checkPoly expr typ = do
  logMeta 20 "checkPoly expr" expr
  logMeta 20 "checkPoly type" typ
  modifyIndent succ
  res <- checkPoly' expr typ
  modifyIndent pred
  logMeta 20 "checkPoly res expr" res
  return res

checkPoly' :: ConcreteM -> Polytype -> VIX AbstractM
checkPoly' expr@(Concrete.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType = do
  (vs, rhoType, f) <- prenexConvert polyType $ instBelowExpr expr
  e <- checkRho expr rhoType
  logShow 25 "checkPoly: prenexConvert vars" vs
  f =<< lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) e

instBelowExpr :: Concrete.Expr v -> InstBelow
instBelowExpr (Concrete.Lam p _ _) = InstBelow p
instBelowExpr _ = InstBelow Explicit

-- inferPoly :: ConcreteM -> InstBelow -> VIX (AbstractM, Polytype)
-- inferPoly expr instBelow = do
--   logMeta 20 "inferPoly expr" expr
--   modifyIndent succ
--   (resExpr, resType) <- inferPoly' expr instBelow
--   modifyIndent pred
--   logMeta 20 "inferPoly res expr" resExpr
--   logMeta 20 "inferPoly res typ" resType
--   return (resExpr, resType)

-- inferPoly' :: ConcreteM -> InstBelow -> VIX (AbstractM, Polytype)
-- inferPoly' expr instBelow = do
--   (expr', exprType) <- inferRho expr instBelow
--   generalise expr' exprType

instantiateForalls :: Polytype -> InstBelow -> VIX (Rhotype, AbstractM -> VIX AbstractM)
instantiateForalls typ instBelow = do
  typ' <- whnf typ
  instantiateForalls' typ' instBelow

instantiateForalls' :: Polytype -> InstBelow -> VIX (Rhotype, AbstractM -> VIX AbstractM)
instantiateForalls' (Abstract.Pi h p t s) (InstBelow p')
  | p < p' = do
    v <- exists h t
    let typ = Util.instantiate1 (pure v) s
    (result, f) <- instantiateForalls typ $ InstBelow p'
    return (result, \x -> f $ betaApp x p $ pure v)
instantiateForalls' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: ConcreteM -> Rhotype -> VIX AbstractM
checkRho expr typ = do
  logMeta 20 "checkRho expr" expr
  logMeta 20 "checkRho type" typ
  modifyIndent succ
  res <- checkRho' expr typ
  modifyIndent pred
  logMeta 20 "checkRho res expr" res
  return res

checkRho' :: ConcreteM -> Rhotype -> VIX AbstractM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: ConcreteM -> InstBelow -> Maybe Rhotype -> VIX (AbstractM, Rhotype)
inferRho expr instBelow expectedAppResult = do
  logMeta 20 "inferRho" expr
  modifyIndent succ
  (resExpr, resType) <- inferRho' expr instBelow expectedAppResult
  modifyIndent pred
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: ConcreteM -> InstBelow -> Maybe Rhotype -> VIX (AbstractM, Rhotype)
inferRho' expr instBelow expectedAppResult = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instBelow) expectedAppResult
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: ConcreteM -> Expected Rhotype -> Maybe Rhotype -> VIX AbstractM
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
  Concrete.Con con -> do
    qc <- resolveConstr con expectedAppResult
    typ <- qconstructor qc
    f <- instExpected expected typ
    f $ Abstract.Con qc
  Concrete.Pi p pat bodyScope -> do
    (pat', _, vs, patType) <- inferPat pat mempty
    let body = instantiatePatternVec pure vs bodyScope
        h = Concrete.patternHint pat
    body' <- enterLevel $ checkPoly body Builtin.Type
    f <- instExpected expected Builtin.Type
    x <- forall h patType
    body'' <- matchSingle (pure x) pat' body' Builtin.Type
    let body''' = body'' >>= unvar (\Match.Fail -> Builtin.Fail Builtin.Type) pure
    f =<< Abstract.Pi h p patType <$> abstract1M x body'''
  Concrete.Lam p pat bodyScope -> do
    let h = Concrete.patternHint pat
    case expected of
      Infer _ _ -> do
        (pat', _, vs, argType) <- inferPat pat mempty
        let body = instantiatePatternVec pure vs bodyScope
        (body', bodyType) <- enterLevel $ inferRho body (InstBelow Explicit) Nothing
        argVar <- forall h argType
        body'' <- matchSingle (pure argVar) pat' body' bodyType
        let body''' = body'' >>= unvar (\Match.Fail -> Builtin.Fail bodyType) pure
        bodyScope' <- abstract1M argVar body'''
        bodyTypeScope <- abstract1M argVar bodyType
        f <- instExpected expected $ Abstract.Pi h p argType bodyTypeScope
        f $ Abstract.Lam h p argType bodyScope'
      Check expectedType -> do
        (typeh, argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        let h' = h <> typeh
        (pat', patExpr, vs) <- checkPat pat mempty argType
        let body = instantiatePatternVec pure vs bodyScope
            bodyType = Util.instantiate1 patExpr bodyTypeScope
        body' <- enterLevel $ checkPoly body bodyType
        argVar <- forall h' argType
        body'' <- matchSingle (pure argVar) pat' body' bodyType
        let body''' = body'' >>= unvar (\Match.Fail -> Builtin.Fail bodyType) pure
        fResult =<< Abstract.Lam h' p argType <$> abstract1M argVar body'''
  Concrete.App fun p arg -> do
    (fun', funType) <- inferRho fun (InstBelow p) expectedAppResult
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
  Concrete.Case e brs -> tcBranches e brs expected
  Concrete.Wildcard -> do
    t <- existsType mempty
    f <- instExpected expected t
    x <- existsVar mempty t
    f x
  Concrete.SourceLoc loc e -> located loc $ tcRho e expected expectedAppResult

typeOfLiteral
  :: Literal
  -> Abstract.Expr v
typeOfLiteral (Integer _) = Builtin.IntType
typeOfLiteral (Byte _) = Builtin.ByteType

tcBranches
  :: ConcreteM
  -> [(Concrete.Pat (PatternScope Concrete.Expr MetaA) (), PatternScope Concrete.Expr MetaA)]
  -> Expected Rhotype
  -> VIX AbstractM
tcBranches expr pbrs expected = do
  (expr', exprType) <- inferRho expr (InstBelow Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) -> do
    (pat', _, _) <- checkPat (void pat) mempty exprType
    let br = instantiatePattern pure pat' brScope
    return (pat', br)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br) -> do
        br' <- checkRho br resType
        return (pat, br')
      return (brs, resType)
    Infer _ instBelow -> case inferredPats of
      [] -> do
        resType <- existsType mempty
        return ([], resType)
      (headPat, headBr):inferredPats' -> do
        (headBr', resType) <- inferRho headBr instBelow Nothing
        brs' <- forM inferredPats' $ \(pat, br) -> do
          br' <- checkRho br resType
          return (pat, br')
        return ((headPat, headBr') : brs', resType)

  f <- instExpected expected resType

  matched <- matchCase expr' inferredBranches resType
  f $ matched >>= unvar (\Match.Fail -> Builtin.Fail resType) pure

--------------------------------------------------------------------------------
-- Patterns
data ExpectedPat
  = InferPat (STRef (World VIX) AbstractM)
  | CheckPat AbstractM

checkPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> Polytype
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
checkPat pat vs expectedType = tcPat pat vs $ CheckPat expectedType

inferPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA, Polytype)
inferPat pat vs = do
  ref <- liftST $ newSTRef $ error "inferPat: empty result"
  (pat', patExpr, vs') <- tcPat pat vs $ InferPat ref
  t <- liftST $ readSTRef ref
  return (pat', patExpr, vs', t)

tcPats
  :: Vector (Concrete.Pat (PatternScope Concrete.Expr MetaA) ())
  -> Vector MetaA
  -> Telescope Plicitness Abstract.Expr MetaA
  -> VIX (Vector (Abstract.Pat AbstractM MetaA, AbstractM, AbstractM), Vector MetaA)
tcPats pats vs tele = do
  unless (Vector.length pats == teleLength tele)
    $ throwError "tcPats length mismatch"
  results <- iforTeleWithPrefixM tele $ \i _ _ s prefix -> do
    let argExprs = snd3 . fst <$> prefix
        vs' | Vector.null prefix = vs
            | otherwise = snd $ Vector.last prefix
        expectedType = instantiateTele id argExprs s
        pat = pats Vector.! i
    (pat', patExpr, vs'') <- checkPat pat vs' expectedType
    return ((pat', patExpr, expectedType), vs'')

  let vs' | Vector.null results = vs
          | otherwise = snd $ Vector.last results
  return (fst <$> results, vs')

tcPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> ExpectedPat
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
tcPat pat vs expected = do
  whenVerbose 20 $ do
    shownPat <- bitraverse (showMeta . instantiatePatternVec pure vs) pure pat
    logPretty 20 "tcPat" shownPat
  logMeta 30 "tcPat vs" vs
  modifyIndent succ
  (pat', patExpr, vs') <- tcPat' pat vs expected
  modifyIndent pred
  logMeta 20 "tcPat res" =<< bitraverse showMeta pure pat'
  logMeta 30 "tcPat vs res" vs'
  return (pat', patExpr, vs')

tcPat'
  :: Concrete.Pat (PatternScope Concrete.Expr MetaA) ()
  -> Vector MetaA
  -> ExpectedPat
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM, Vector MetaA)
tcPat' pat vs expected = case pat of
  Concrete.VarPat h () -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType h
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall h expectedType
    return (Abstract.VarPat h v, pure v, vs <> pure v)
  Concrete.WildcardPat -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType mempty
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall mempty expectedType
    return (Abstract.WildcardPat, pure v, vs)
  Concrete.LitPat lit -> do
    (p, e) <- instPatExpected
      expected
      Builtin.IntType
      (Abstract.LitPat lit)
      (Abstract.Lit lit)
    return (p, e, vs)
  Concrete.ConPat c pats -> do
    qc@(QConstr typeName _) <- resolveConstr c $ case expected of
      CheckPat expectedType -> Just expectedType
      InferPat _ -> Nothing
    (_, typeType) <- definition typeName
    conType <- qconstructor qc

    let paramsTele = telescope typeType
        numParams = teleLength paramsTele
        (tele, retScope) = pisView conType
        argPlics = Vector.drop numParams $ teleAnnotations tele

    pats' <- Vector.fromList <$> exactlyEqualisePats (Vector.toList argPlics) (Vector.toList pats)

    paramVars <- forTeleWithPrefixM paramsTele $ \h _ s paramVars ->
      exists h $ instantiateTele pure paramVars s

    let argTele = instantiatePrefix (pure <$> paramVars) tele

    (pats'', vs') <- tcPats (snd <$> pats') vs argTele

    let argExprs = snd3 <$> pats''
        argTypes = thd3 <$> pats''
        pats''' = Vector.zip3 argPlics (fst3 <$> pats'') argTypes
        params = Vector.zip (teleAnnotations paramsTele) $ pure <$> paramVars
        patExpr = apps (Abstract.Con qc) $ ((\v -> (Implicit, pure v)) <$> paramVars) <> Vector.zip argPlics argExprs

        retType = instantiateTele id (pure <$> paramVars <|> argExprs) retScope

    (p, patExpr') <- instPatExpected expected retType (Abstract.ConPat qc params pats''') patExpr

    return (p, patExpr', vs')
  Concrete.AnnoPat s p -> do
    let patType = instantiatePatternVec pure vs s
    patType' <- checkPoly patType Builtin.Type
    (p', patExpr, vs') <- checkPat p vs patType'
    (p'', patExpr') <- instPatExpected expected patType' p' patExpr
    return (p'', patExpr', vs')
  Concrete.ViewPat _ _ -> throwError "tcPat ViewPat undefined TODO"
  Concrete.PatLoc loc p -> located loc $ tcPat' p vs expected

instPatExpected
  :: ExpectedPat
  -> Polytype -- ^ patType
  -> Abstract.Pat AbstractM MetaA -- ^ pat
  -> AbstractM -- ^ :: patType
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM) -- ^ (pat :: expectedType, :: expectedType)
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
  -> (AbstractM -> VIX AbstractM) -- ^ expectedType -> patType
  -> VIX (Abstract.Pat AbstractM MetaA, AbstractM) -- ^ (expectedType, :: expectedType)
viewPat expectedType pat patExpr f = do
  x <- forall mempty expectedType
  fx <- f $ pure x
  if fx == pure x then
    return (pat, patExpr)
  else do
    fExpr <- Abstract.Lam mempty Explicit expectedType <$> abstract1M x fx
    return (Abstract.ViewPat fExpr pat, pure x)

patToTerm
  :: Abstract.Pat AbstractM MetaA
  -> AbstractM
  -> VIX (Maybe AbstractM)
patToTerm pat typ = case pat of
  Abstract.VarPat _ v -> return $ Just $ Abstract.Var v
  Abstract.WildcardPat -> do
    res <- exists mempty typ
    return $ Just $ pure res
  Abstract.ConPat qc params pats -> do
    mterms <- mapM (\(p, pat', typ') -> fmap ((,) p) <$> patToTerm pat' typ') pats
    case sequence mterms of
      Nothing -> return Nothing
      Just terms -> return $ Just $
        apps (Abstract.Con qc) $ params <> terms
  Abstract.LitPat l -> return $ Just $ Abstract.Lit l
  Abstract.ViewPat{} -> return Nothing

{-
instantiateDataType
  :: Applicative f
  => Name
  -> VIX (AbstractM, Vector (Plicitness, f MetaA))
instantiateDataType typeName = mdo
  (_, dataTypeType) <- definition typeName
  let params = telescope dataTypeType
      inst = instantiateTele (pure . snd) paramVars
  paramVars <- forMTele params $ \h p s -> do
    v <- exists h (inst s)
    return (p, v)
  let pureParamVars = fmap pure <$> paramVars
      dataType = apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (Implicit, pure v)) <$> paramVars
  return (dataType, implicitParamVars)
-}

--------------------------------------------------------------------------------
-- Constrs
resolveConstr
  :: Either Constr QConstr
  -> Maybe Rhotype
  -> VIX QConstr
resolveConstr (Left c) expected = do
  typeName <- resolveConstrsType [Left c] expected
  return (QConstr typeName c)
resolveConstr (Right qc) _ = return qc

resolveConstrsType
  :: [Either Constr QConstr]
  -> Maybe Rhotype
  -> VIX Name
resolveConstrsType cs expected = do
  mExpectedType <- expectedDataType
  possibleTypeSets <- forM cs $ \c -> do
    possibleTypes <- constructor c
    return $ Set.map fst (possibleTypes :: Set (Name, Abstract.Expr ()))
  let possibleTypes = List.foldl1' Set.intersection possibleTypeSets

  when (Set.null possibleTypes) $
    err
      "No such data type"
      ["There is no data type with the" Leijen.<+> constrDoc <> "."]

  let candidateTypes
        = maybe
          possibleTypes
          (Set.intersection possibleTypes . Set.singleton)
          mExpectedType

  case (Set.toList candidateTypes, mExpectedType) of
    ([], Just expectedType) ->
      err "Undefined constructor"
        [ Leijen.dullgreen (pretty expectedType)
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
    findExpectedDataType :: AbstractM -> VIX (Maybe Name)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h _ t s -> do
          v <- forall h t
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
        $ Err (Just heading) docs mempty
    constrDoc = case either (Leijen.red . pretty) (Leijen.red . pretty) <$> cs of
      [pc] -> "constructor" Leijen.<+> pc
      pcs -> "constructors" Leijen.<+> prettyHumanList "and" pcs

--------------------------------------------------------------------------------
-- Prenex conversion/deep skolemisation
-- | prenexConvert t1 = (vs, t2, f) => f : t2 -> t1
prenexConvert
  :: Polytype
  -> InstBelow
  -> VIX (Vector (Plicitness, MetaA), Rhotype, AbstractM -> VIX AbstractM)
prenexConvert typ instBelow = do
  typ' <- whnf typ
  prenexConvert' typ' instBelow

prenexConvert'
  :: Polytype
  -> InstBelow
  -> VIX (Vector (Plicitness, MetaA), Rhotype, AbstractM -> VIX AbstractM)
prenexConvert' (Abstract.Pi h p t resScope) (InstBelow p') | p < p' = do
  y <- forall h t
  let resType = Util.instantiate1 (pure y) resScope
  (vs, resType', f) <- prenexConvert resType $ InstBelow p'
  return $ case p of
    Implicit ->
      ( Vector.cons (p, y) vs
      , resType'
      , \x -> fmap (lam h p t) $ abstract1M y
        =<< f (betaApp x p $ pure y)
      )
    Explicit ->
      ( vs
      , Abstract.Pi h p t $ abstract1 y resType'
      , \x -> fmap (Abstract.Lam h p t) . abstract1M y
        =<< f
        =<< lams <$> metaTelescopeM vs
        <*> abstractM (teleAbstraction $ snd <$> vs)
        (betaApp (betaApps x $ second pure <$> vs) p $ pure y)
      )
prenexConvert' typ _ = return (mempty, typ, pure)

--------------------------------------------------------------------------------
-- Subtyping/subsumption
-- | subtype t1 t2 = f => f : t1 -> t2
subtype :: Polytype -> Polytype -> VIX (AbstractM -> VIX AbstractM)
subtype typ1 typ2 = do
  logMeta 30 "subtype t1" typ1
  logMeta 30 "        t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtype' typ1' typ2'
  modifyIndent pred
  return res

subtype' :: Polytype -> Polytype -> VIX (AbstractM -> VIX AbstractM)
subtype' (Abstract.Pi h1 p1 argType1 retScope1) (Abstract.Pi h2 p2 argType2 retScope2)
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h argType2
    v1 <- f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- subtype retType1 retType2
    return
      $ \x -> fmap (lam h p2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x p1 v1)
subtype' typ1 typ2 = do
  (as, rho, f1) <- prenexConvert typ2 $ InstBelow Explicit
  f2 <- subtypeRho typ1 rho $ InstBelow Explicit
  return $ \x ->
    f1 =<< lams <$> metaTelescopeM as
    <*> (abstractM (teleAbstraction $ snd <$> as) =<< f2 x)

subtypeRho :: Polytype -> Rhotype -> InstBelow -> VIX (AbstractM -> VIX AbstractM)
subtypeRho typ1 typ2 instBelow = do
  logMeta 30 "subtypeRho t1" typ1
  logMeta 30 "           t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtypeRho' typ1' typ2' instBelow
  modifyIndent pred
  return res

subtypeRho' :: Polytype -> Rhotype -> InstBelow -> VIX (AbstractM -> VIX AbstractM)
subtypeRho' typ1 typ2 _ | typ1 == typ2 = return pure
subtypeRho' (Abstract.Pi h1 p1 argType1 retScope1) (Abstract.Pi h2 p2 argType2 retScope2) _
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h argType2
    v1 <- f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- subtypeRho retType1 retType2 $ InstBelow Explicit
    return
      $ \x -> fmap (lam h p2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x p1 v1)
subtypeRho' (Abstract.Pi h p t s) typ2 (InstBelow p') | p < p' = do
  v <- exists h t
  f <- subtypeRho (Util.instantiate1 (pure v) s) typ2 $ InstBelow p'
  return $ \x -> f $ Abstract.App x p $ pure v
subtypeRho' typ1 typ2 _ = do
  unify [] typ1 typ2
  return pure

-- | funSubtypes typ ps = (ts, retType, f) => f : (ts -> retType) -> typ
funSubtypes
  :: Rhotype
  -> Vector Plicitness
  -> VIX
    ( Telescope Plicitness Abstract.Expr MetaA
    , Scope Tele Abstract.Expr MetaA
    , Vector (AbstractM -> VIX AbstractM)
    )
funSubtypes startType plics = go plics startType mempty mempty mempty
  where
    go ps typ vs tele fs
      | Vector.null ps = do
        let vars = Vector.reverse $ Vector.fromList vs
            funs = Vector.reverse $ Vector.fromList fs
            abstr = teleAbstraction vars
        tele' <- forM (Vector.reverse $ Vector.fromList tele) $ \(h, p, t) -> do
          s <- abstractM abstr t
          return (h, p, s)

        typeScope <- abstractM abstr typ

        return (Telescope tele', typeScope, funs)
      | otherwise = do
        let p = Vector.head ps
        (h, argType, resScope, f) <- funSubtype typ p
        v <- forall mempty argType
        go
          (Vector.tail ps)
          (Util.instantiate1 (pure v) resScope)
          (v : vs)
          ((h, p, argType) : tele)
          (f : fs)

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> VIX (NameHint, Rhotype, Scope1 Abstract.Expr MetaA, AbstractM -> VIX AbstractM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> VIX (NameHint, Rhotype, Scope1 Abstract.Expr MetaA, AbstractM -> VIX AbstractM)
funSubtype' (Abstract.Pi h p t s) p' | p == p' = return (h, t, s, pure)
funSubtype' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtypeRho' (Abstract.Pi mempty p argType resScope) typ $ InstBelow p
  return (mempty, argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> VIX (Rhotype, Scope1 Abstract.Expr MetaA, AbstractM -> VIX AbstractM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> VIX (Rhotype, Scope1 Abstract.Expr MetaA, AbstractM -> VIX AbstractM)
subtypeFun' (Abstract.Pi _ p t s) p' | p == p' = return (t, s, pure)
subtypeFun' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtype typ $ Abstract.Pi mempty p argType resScope
  return (argType, resScope, f)

--------------------------------------------------------------------------------
-- Generalisation
generalise
  :: AbstractM
  -> AbstractM
  -> VIX (AbstractM, AbstractM)
generalise expr typ = do
  -- fvs <- (<>) <$> foldMapM (:[]) typ' <*> foldMapM (:[]) expr
  fvs <- foldMapM (:[]) typ -- <*> foldMapM (:[]) expr'
  l <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HashSet.fromList <$> filterM p fvs

  deps <- forM (HashSet.toList fvs') $ \x -> do
    ds <- foldMapM HashSet.singleton $ metaType x
    return (x, ds)

  let sorted = map go $ topoSort deps
  genexpr <- foldrM (\v e -> lam (metaHint v) Implicit (metaType v) <$> abstract1M v e) expr sorted
  gentype <- foldrM (\v e -> pi_ (metaHint v) Implicit (metaType v) <$> abstract1M v e) typ sorted

  return (genexpr, gentype)
  where
    go [v] = v
    go _ = error "Generalise"

--------------------------------------------------------------------------------
-- Definitions
checkConstrDef
  :: ConstrDef ConcreteM
  -> VIX (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c typ) = do
  typ' <- zonk =<< checkPoly typ Builtin.Type
  (sizes, ret) <- go typ'
  let size = foldr Builtin.addInt (Abstract.Lit $ Integer 0) sizes
  return (ConstrDef c typ', ret, size)
  where
    go :: AbstractM -> VIX ([AbstractM], AbstractM)
    go (Abstract.Pi h _ t s) = do
      v <- forall h t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      return (t : sizes, ret)
    go ret = return ([], ret)

checkDataType
  :: MetaA
  -> DataDef Concrete.Expr MetaA
  -> AbstractM
  -> VIX (DataDef Abstract.Expr MetaA, AbstractM, AbstractM)
checkDataType name (DataDef cs) typ = do
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  ps' <- forTeleWithPrefixM (telescope typ') $ \h p s ps' -> do
    let is = instantiateTele pure (snd <$> ps') s
    v <- forall h is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

  mapM_ (unify [] constrRetType) rets

  tagSize <- gets $ Target.intBytes . vixTarget

  let addTagSize = case cs of
        [] -> id
        [_] -> id
        _ -> Builtin.addInt $ Abstract.Lit $ Integer tagSize

      typeSize = addTagSize
               $ foldr Builtin.maxInt (Abstract.Lit $ Integer 0) sizes

  unify [] Builtin.Type =<< typeOfM constrRetType

  abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
    logMeta 20 ("checkDataType res " ++ show qc) e
    traverse (abstractM abstr) c

  params <- metaTelescopeM ps'
  let typ'' = pis params $ Scope Builtin.Type

  typeSize' <- whnf' True typeSize
  abstractedTypeSize <- abstractM abstr typeSize'

  return (DataDef abstractedCs, lams params abstractedTypeSize, typ'')

checkClauses
  :: NonEmpty (Concrete.Clause Concrete.Expr MetaA)
  -> Polytype
  -> VIX AbstractM
checkClauses clauses polyType = do
  forM_ clauses $ logMeta 20 "checkClauses clause"
  logMeta 20 "checkClauses typ" polyType

  modifyIndent succ

  (vs, rhoType, f) <- prenexConvert polyType $ minimum $ instBelowClause <$> clauses

  ps <- piPlicitnesses rhoType

  clauses' <- forM clauses $ \(Concrete.Clause pats body) -> do
    pats' <- equalisePats ps $ Vector.toList pats
    return $ Concrete.Clause (Vector.fromList pats') body

  let equalisedClauses = equaliseClauses clauses'

  forM_ equalisedClauses $ logMeta 20 "checkClauses equalisedClause"

  res <- checkClausesRho equalisedClauses rhoType

  modifyIndent pred
  logMeta 20 "checkClauses res" res

  f =<< lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) res
  where
    instBelowClause :: Concrete.Clause Concrete.Expr v -> InstBelow
    instBelowClause (Concrete.Clause pats s)
      | Vector.length pats > 0 = InstBelow $ fst $ Vector.head pats
      | otherwise = instBelowExpr $ fromScope s

    piPlicitnesses :: AbstractM -> VIX [Plicitness]
    piPlicitnesses t = do
      t' <- whnf t
      piPlicitnesses' t'

    piPlicitnesses' :: AbstractM -> VIX [Plicitness]
    piPlicitnesses' (Abstract.Pi h p t s) = do
      v <- forall h t
      (:) p <$> piPlicitnesses (instantiate1 (pure v) s)
    piPlicitnesses' _ = return mempty

checkClausesRho
  :: NonEmpty (Concrete.Clause Concrete.Expr MetaA)
  -> Rhotype
  -> VIX AbstractM
checkClausesRho clauses rhoType = do
  forM_ clauses $ logMeta 20 "checkClausesRho clause"
  logMeta 20 "checkClausesRho type" rhoType

  let (ps, firstPats) = Vector.unzip ppats
        where
          Concrete.Clause ppats _ = NonEmpty.head clauses
  (argTele, returnTypeScope, fs) <- funSubtypes rhoType ps

  modifyIndent succ

  clauses' <- forM clauses $ \(Concrete.Clause pats bodyScope) -> do
    (pats', patVars) <- tcPats (snd <$> pats) mempty argTele
    let body = instantiatePatternVec pure patVars bodyScope
        argExprs = snd3 <$> pats'
        returnType = instantiateTele id argExprs returnTypeScope
    body' <- checkRho body returnType
    return (fst3 <$> pats', body')

  modifyIndent pred

  forM_ clauses' $ \(pats, body) -> do
    forM_ pats $ \pat -> logMeta 20 "checkClausesRho clause pat" =<< bitraverse showMeta pure pat
    logMeta 20 "checkClausesRho clause body" body

  argVars <- forTeleWithPrefixM (addTeleNames argTele $ Concrete.patternHint <$> firstPats) $ \h _ s argVars ->
    forall h $ instantiateTele pure argVars s

  let returnType = instantiateTele pure argVars returnTypeScope

  body <- matchClauses
    (Vector.toList $ pure <$> argVars)
    (NonEmpty.toList $ first Vector.toList <$> clauses')
    returnType

  let body' = body >>= unvar (\Match.Fail -> Builtin.Fail returnType) pure

  logMeta 25 "checkClausesRho body res" body'

  result <- foldrM
    (\(p, (f, v)) e ->
      f =<< Abstract.Lam (metaHint v) p (metaType v) <$> abstract1M v e)
    body'
    (Vector.zip ps $ Vector.zip fs argVars)

  logMeta 20 "checkClausesRho res" result
  return result

checkDefType
  :: MetaA
  -> Concrete.PatDefinition Concrete.Expr MetaA
  -> SourceLoc
  -> AbstractM
  -> VIX (Definition Abstract.Expr MetaA, AbstractM)
checkDefType v def loc typ = located (render loc) $ case def of
  Concrete.PatDefinition clauses -> do
    e' <- checkClauses clauses typ
    return (Definition e', typ)
  Concrete.PatDataDefinition d -> do
    (d', rep, typ') <- checkDataType v d typ
    return (DataDefinition d' rep, typ')

generaliseDef
  :: Vector MetaA
  -> Definition Abstract.Expr MetaA
  -> AbstractM
  -> VIX ( Definition Abstract.Expr MetaA
         , AbstractM
         )
generaliseDef vs (Definition e) t = do
  let ivs = (,) Implicit <$> vs
  ge <- abstractMs ivs lam e
  gt <- abstractMs ivs pi_ t
  return (Definition ge, gt)
generaliseDef vs (DataDefinition (DataDef cs) rep) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
      ivs = (,) Implicit <$> vs
  -- Abstract vs on top of typ
  grep <- abstractMs ivs lam rep
  gtyp <- abstractMs ivs pi_ typ
  return (DataDefinition (DataDef cs') grep, gtyp)
  where
    f v = pure $ maybe (F v) (B . Tele) (v `Vector.elemIndex` vs)
    g = pure . B . (+ Tele (length vs))
generaliseDef vs Opaque typ = do
  unless (Vector.null vs) $
    throwError "generaliseDef opaque"
  return (Opaque, typ)

abstractMs
  :: Foldable t
  => t (Plicitness, MetaA)
  -> (NameHint -> Plicitness -> AbstractM -> ScopeM () Abstract.Expr -> AbstractM)
  -> AbstractM
  -> VIX AbstractM
abstractMs vs c b = foldrM
  (\(p, v)  s -> c (metaHint v) p (metaType v) <$> abstract1M v s)
  b
  vs

generaliseDefs
  :: Vector ( MetaA
            , Definition Abstract.Expr MetaA
            , AbstractM
            )
  -> VIX (Vector ( Definition Abstract.Expr MetaA
                 , AbstractM
                 )
         )
generaliseDefs xs = do
  modifyIndent succ

  fvs <- asum <$> mapM (foldMapM (:[])) types

  l <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HashSet.fromList <$> filterM p fvs

  deps <- forM (HashSet.toList fvs') $ \x -> do
    ds <- foldMapM HashSet.singleton $ metaType x
    return (x, ds)

  let sortedFvs = map impure $ topoSort deps
      appl x = apps x [(Implicit, pure fv) | fv <- sortedFvs]
      instVars = appl . pure <$> vars

  instDefs <- forM xs $ \(_, d, t) -> do
    d' <- boundJoin <$> traverse (sub instVars) d
    t' <- join <$> traverse (sub instVars) t
    return (d', t')

  genDefs <- mapM (uncurry $ generaliseDef $ Vector.fromList sortedFvs) instDefs

  modifyIndent pred

  return genDefs
  where
    vars  = (\(v, _, _) -> v) <$> xs
    types = (\(_, _, t) -> t) <$> xs
    sub instVars v | Just x <- v `Vector.elemIndex` vars
      = return $ fromMaybe (error "generaliseDefs") $ instVars Vector.!? x
    sub instVars v@(metaRef -> Just r) = do
      sol <- solution r
      case sol of
        Left _ -> return $ pure v
        Right s -> join <$> traverse (sub instVars) s
    sub _ v = return $ pure v
    impure [a] = a
    impure _ = error "generaliseDefs"

checkRecursiveDefs
  :: Vector ( Name
            , SourceLoc
            , Concrete.PatDefinition Concrete.Expr Void
            , Concrete.Expr Void
            )
  -> VIX (Vector ( Name
                 , Definition Abstract.Expr Void
                 , Abstract.Expr Void
                 )
         )
checkRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  (checkedDefs, evars) <- enterLevel $ do
    evars <- Vector.forM names $ \name -> do
      let hint = fromName name
      typ <- existsType hint
      forall hint typ

    let expose name = case Vector.elemIndex name names of
          Nothing -> global name
          Just index -> pure
            $ fromMaybe (error "checkRecursiveDefs 1")
            $ evars Vector.!? index

    let exposedDefs = flip fmap defs $ \(_, loc, def, typ) ->
          (loc, bound absurd expose def, bind absurd expose typ)

    checkedDefs <- forM (Vector.zip evars exposedDefs) $ \(evar, (loc, def, typ)) -> do
      typ' <- checkPoly typ Builtin.Type
      unify [] (metaType evar) typ'
      (def', typ'') <- checkDefType evar def loc typ'
      logMeta 20 ("checkRecursiveDefs res " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) def'
      logMeta 20 ("checkRecursiveDefs res t " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) typ''
      return (loc, (evar, def', typ''))

    detectTypeRepCycles checkedDefs
    detectDefCycles checkedDefs

    return (checkedDefs, evars)

  genDefs <- generaliseDefs $ snd <$> checkedDefs

  let unexpose evar = case Vector.elemIndex evar evars of
        Nothing -> pure evar
        Just index -> global
          $ fromMaybe (error "checkRecursiveDefs 2")
          $ names Vector.!? index
      vf :: MetaA -> VIX b
      vf v = throwError $ "checkRecursiveDefs " ++ show v

  forM (Vector.zip names genDefs) $ \(name, (def, typ)) -> do
    let unexposedDef = bound unexpose global def
        unexposedTyp = bind unexpose global typ
    unexposedDef' <- traverse vf unexposedDef
    unexposedTyp' <- traverse vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')
