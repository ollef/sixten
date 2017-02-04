{-# LANGUAGE OverloadedStrings, RecursiveDo, ScopedTypeVariables, TypeFamilies, ViewPatterns #-}
module Infer where

import Control.Monad.Except
import Control.Monad.ST()
import Control.Monad.ST.Class
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
import Text.Trifecta.Result(Err(Err), explain)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen

import qualified Builtin
import Match
import Match.Pattern as Match
import Meta
import Normalise
import Simplify
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import TCM
import TopoSort
import TypeOf
import Unify
import Util

type Polytype = AbstractM
type Monotype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

newtype InstBelow = InstBelow Plicitness

data Expected typ
  = Infer (STRef (World TCM) typ) InstBelow
  | Check typ

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected Rhotype -> Polytype -> TCM (AbstractM -> TCM AbstractM)
instExpected (Infer r instBelow) t = do
  (t', f) <- instantiateForalls t instBelow
  liftST $ writeSTRef r t'
  return f
instExpected (Check t2) t1 = subtype t1 t2

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: ConcreteM -> Polytype -> TCM AbstractM
checkPoly expr typ = do
  logMeta 20 "checkPoly expr" expr
  logMeta 20 "checkPoly type" typ
  modifyIndent succ
  res <- checkPoly' expr typ
  modifyIndent pred
  logMeta 20 "checkPoly res expr" res
  return res

checkPoly' :: ConcreteM -> Polytype -> TCM AbstractM
checkPoly' expr@(Concrete.Lam Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType = do
  (vs, rhoType, f) <- prenexConvert polyType
  e <- checkRho expr rhoType
  logShow 25 "checkPoly: prenexConvert vars" vs
  f =<< lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) e

-- inferPoly :: ConcreteM -> Plicitness -> TCM (AbstractM, Polytype)
-- inferPoly expr maxPlicitness = do
--   logMeta 20 "inferPoly expr" expr
--   modifyIndent succ
--   (resExpr, resType) <- inferPoly' expr maxPlicitness
--   modifyIndent pred
--   logMeta 20 "inferPoly res expr" resExpr
--   logMeta 20 "inferPoly res typ" resType
--   return (resExpr, resType)

-- inferPoly' :: ConcreteM -> Plicitness -> TCM (AbstractM, Polytype)
-- inferPoly' expr maxPlicitness = do
--   (expr', exprType) <- inferRho expr maxPlicitness
--   generalise expr' exprType

instantiateForalls :: Polytype -> InstBelow -> TCM (Rhotype, AbstractM -> TCM AbstractM)
instantiateForalls typ instBelow = do
  typ' <- whnf typ
  instantiateForalls' typ' instBelow

instantiateForalls' :: Polytype -> InstBelow -> TCM (Rhotype, AbstractM -> TCM AbstractM)
instantiateForalls' (Abstract.Pi h p t s) (InstBelow p')
  | p < p' = do
    v <- exists h t
    let typ = Util.instantiate1 (pure v) s
    (result, f) <- instantiateForalls typ $ InstBelow p'
    return (result, \x -> f $ betaApp x p $ pure v)
instantiateForalls' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: ConcreteM -> Rhotype -> TCM AbstractM
checkRho expr typ = do
  logMeta 20 "checkRho expr" expr
  logMeta 20 "checkRho type" typ
  modifyIndent succ
  res <- checkRho' expr typ
  modifyIndent pred
  logMeta 20 "checkRho res expr" res
  return res

checkRho' :: ConcreteM -> Rhotype -> TCM AbstractM
checkRho' expr ty = tcRho expr (Check ty) (Just ty)

inferRho :: ConcreteM -> InstBelow -> Maybe Rhotype -> TCM (AbstractM, Rhotype)
inferRho expr instBelow expectedAppResult = do
  logMeta 20 "inferRho" expr
  modifyIndent succ
  (resExpr, resType) <- inferRho' expr instBelow expectedAppResult
  modifyIndent pred
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: ConcreteM -> InstBelow -> Maybe Rhotype -> TCM (AbstractM, Rhotype)
inferRho' expr instBelow expectedAppResult = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr (Infer ref instBelow) expectedAppResult
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: ConcreteM -> Expected Rhotype -> Maybe Rhotype -> TCM AbstractM
tcRho expr expected expectedAppResult = case expr of
  Concrete.Var v -> do
    f <- instExpected expected $ metaType v
    f $ Abstract.Var v
  Concrete.Global g -> do
    (_, typ) <- definition g
    f <- instExpected expected typ
    f $ Abstract.Global g
  Concrete.Lit l -> do
    f <- instExpected expected Builtin.Size
    f $ Abstract.Lit l
  Concrete.Con con -> do
    typeName <- resolveConstrType [con] expectedAppResult
    let qc = qualify typeName con
    typ <- qconstructor qc
    f <- instExpected expected typ
    f $ Abstract.Con qc
  Concrete.Pi p pat bodyScope -> do
    (pat', vs, patType) <- inferPat pat mempty
    let body = instantiatePatternVec pure vs bodyScope
        h = Concrete.patternHint pat
    body' <- enterLevel $ checkPoly body =<< existsTypeType mempty
    f <- instExpected expected $ Builtin.TypeP $ Abstract.Lit 1
    x <- forall h p patType
    body'' <- matchSingle (pure x) pat' body'
    f =<< Abstract.Pi h p patType <$> abstract1M x body''
  Concrete.Lam p pat bodyScope -> do
    let h = Concrete.patternHint pat
    case expected of
      Infer _ _ -> do
        (pat', vs, argType) <- inferPat pat mempty
        argVar <- forall h p argType
        let body = instantiatePatternVec pure vs bodyScope
        (body', bodyType) <- enterLevel $ inferRho body (InstBelow Explicit) Nothing
        body'' <- matchSingle (pure argVar) pat' body'
        bodyScope' <- abstract1M argVar body''
        bodyTypeScope <- abstract1M argVar bodyType
        f <- instExpected expected $ Abstract.Pi h p argType bodyTypeScope
        f $ Abstract.Lam h p argType bodyScope'
      Check expectedType -> do
        (argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        (pat', vs) <- checkPat pat mempty argType
        argVar <- forall h p argType
        let body = instantiatePatternVec pure vs bodyScope
            bodyType = Util.instantiate1 (pure argVar) bodyTypeScope
        body' <- enterLevel $ checkPoly body bodyType
        body'' <- matchSingle (pure argVar) pat' body'
        fResult =<< Abstract.Lam h p argType <$> abstract1M argVar body''
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

tcBranches
  :: ConcreteM
  -> [(Concrete.Pat (PatternScope Concrete.Expr MetaP) (), PatternScope Concrete.Expr MetaP)]
  -> Expected Rhotype
  -> TCM AbstractM
tcBranches expr pbrs expected = do
  (expr', exprType) <- inferRho expr (InstBelow Explicit) Nothing

  inferredPats <- forM pbrs $ \(pat, brScope) -> do
    (pat', _) <- checkPat (void pat) mempty exprType
    let br = instantiatePattern pure pat' brScope
    return (pat', br)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPats $ \(pat, br) -> do
        br' <- checkRho br resType
        return (pat, br')
      return (brs, resType)
    Infer _ maxPlicitness -> case inferredPats of
      [] -> do
        resType <- existsType mempty
        return ([], resType)
      (headPat, headBr):inferredPats' -> do
        (headBr', resType) <- inferRho headBr maxPlicitness Nothing
        brs' <- forM inferredPats' $ \(pat, br) -> do
          br' <- checkRho br resType
          return (pat, br')
        return ((headPat, headBr') : brs', resType)

  f <- instExpected expected resType

  matched <- case inferredBranches of
    [] -> return $ Abstract.Case expr' $ NoBranches resType
    _ -> matchCase expr' inferredBranches

  f matched

--------------------------------------------------------------------------------
-- Patterns
instPatExpected
  :: Expected Polytype
  -> Polytype
  -> TCM (AbstractM, AbstractM -> TCM AbstractM) -- ^ (expectedType, expectedType -> patType)
instPatExpected (Check expectedType) patType = do
  f <- subtype expectedType patType
  return (expectedType, f)
instPatExpected (Infer r _maxPlicitness) patType = do
  liftST $ writeSTRef r patType
  return (patType, return)

checkPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaP) ()
  -> Vector MetaP
  -> Polytype
  -> TCM (Match.Pat AbstractM MetaP, Vector MetaP)
checkPat pat vs expectedType = tcPat pat vs $ Check expectedType

checkPats
  :: Vector (Concrete.Pat (PatternScope Concrete.Expr MetaP) ())
  -> Vector Polytype
  -> TCM (Vector (Match.Pat AbstractM MetaP), Vector MetaP)
checkPats pats types = do
  unless (Vector.length pats == Vector.length types)
    $ throwError "checkPats length mismatch"
  (results, vs) <- foldlM go mempty $ Vector.zip pats types
  return (Vector.reverse $ Vector.fromList results, vs)
  where
    go (resultPats, vs) (pat, typ) = do
      (resultPat, vs') <- checkPat pat vs typ
      return (resultPat : resultPats, vs')

inferPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaP) ()
  -> Vector MetaP
  -> TCM (Match.Pat AbstractM MetaP, Vector MetaP, Polytype)
inferPat pat vs = do
  ref <- liftST $ newSTRef $ error "inferPat: empty result"
  (pat', vs') <- tcPat pat vs $ Infer ref $ InstBelow Explicit -- TODO instBelow?
  typ <- liftST $ readSTRef ref
  return (pat', vs', typ)

tcPat
  :: Concrete.Pat (PatternScope Concrete.Expr MetaP) ()
  -> Vector MetaP
  -> Expected Polytype
  -> TCM (Match.Pat AbstractM MetaP, Vector MetaP)
tcPat pat vs expected = do
  whenVerbose 20 $ do
    shownPat <- bitraverse (showMeta . instantiatePatternVec pure vs) pure pat
    logPretty 20 "tcPat" shownPat
  logMeta 30 "tcPat vs" vs
  modifyIndent succ
  (pat', vs') <- tcPat' pat vs expected
  modifyIndent pred
  logMeta 20 "tcPat res" (first (const ()) pat')
  logMeta 30 "tcPat vs res" vs'
  return (pat', vs')

tcPat'
  :: Concrete.Pat (PatternScope Concrete.Expr MetaP) ()
  -> Vector MetaP
  -> Expected Polytype
  -> TCM (Match.Pat AbstractM MetaP, Vector MetaP)
tcPat' pat vs expected = case pat of
  Concrete.VarPat h () -> do
    varType <- case expected of
      Infer ref _maxPlicitness -> do
        varType <- existsType h
        liftST $ writeSTRef ref varType
        return varType
      Check varType -> return varType
    v <- forall h Explicit varType
    return (Match.VarPat h v, vs <> pure v)
  Concrete.WildcardPat -> return (Match.WildcardPat, vs)
  Concrete.LitPat lit -> do
    (expectedType, f) <- instPatExpected expected Builtin.Size
    p <- viewPat expectedType f $ Match.LitPat lit
    return (p, vs)
  Concrete.ConPat c pats -> do
    typeName <- resolveConstrType [c] $ case expected of
      Infer _ _ -> Nothing
      Check expectedType -> Just expectedType
    let qc = qualify typeName c
    (_, typeType) <- definition typeName
    conType <- qconstructor qc
    -- TODO check plicitnesses
    -- TODO Make a function that checks a list of patterns against a type properly
    let (paramsTele, _) = pisView (typeType :: AbstractM)
        numParams = teleLength paramsTele
        (tele, retScope) = pisView conType

    typeVars <- mdo
      typeVars <- forMTele tele $ \h _ s ->
        exists h $ instantiateTele pure typeVars s
      return typeVars

    let retType = instantiateTele pure typeVars retScope
    unless (Vector.length pats == Vector.length typeVars - numParams) $
      throwError $ "tcPat wrong number of args " ++ show qc ++ " " ++ show pats

    let go (revPats, vs') ((p, pat'), v) = do
          (pat'', vs'') <- checkPat pat' vs' $ metaType v
          return ((p, pat'', metaType v) : revPats, vs'')
          -- TODO unify the var with the pat

    (revPats, vs') <- foldlM go (mempty, vs)
      $ Vector.zip pats
      $ Vector.drop numParams typeVars
    let pats' = Vector.fromList $ reverse revPats

    (expectedType, f) <- instPatExpected expected retType
    p <- viewPat expectedType f $ Match.ConPat qc pats'

    return (p, vs')
  Concrete.AnnoPat s p -> do
    let patType = instantiatePatternVec pure vs s
    patType' <- checkPoly patType =<< existsTypeType (Concrete.patternHint p)
    (p', vs') <- checkPat p vs patType'
    (expectedType, f) <- instPatExpected expected patType'
    p'' <- viewPat expectedType f p'
    return (p'', vs')
  Concrete.ViewPat _ _ -> throwError "tcPat ViewPat undefined TODO"
  Concrete.PatLoc loc p -> located loc $ tcPat' p vs expected

viewPat
  :: AbstractM -- ^ expectedType
  -> (AbstractM -> TCM AbstractM) -- ^ expectedType -> patType
  -> Match.Pat AbstractM MetaP
  -> TCM (Match.Pat AbstractM MetaP) -- ^ expectedType
viewPat expectedType f p = do
  x <- forall mempty Explicit expectedType
  fx <- f $ pure x
  if fx == pure x then
    return p
  else do
    fExpr <- Abstract.Lam mempty Explicit expectedType <$> abstract1M x fx
    return $ Match.ViewPat fExpr p

{-
instantiateDataType
  :: Applicative f
  => Name
  -> TCM (AbstractM, Vector (Plicitness, f MetaP))
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
resolveConstrType
  :: [Either Constr QConstr]
  -> Maybe Rhotype
  -> TCM Name
resolveConstrType cs expected = do
  mExpectedType <- expectedDataType
  possibleTypeSets <- forM cs $ \c -> do
    possibleTypes <- constructor c
    return $ Set.map fst (possibleTypes :: Set (Name, Abstract.ExprP ()))
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
    findExpectedDataType :: AbstractM -> TCM (Maybe Name)
    findExpectedDataType typ = do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h p t s -> do
          v <- forall h p t
          findExpectedDataType $ Util.instantiate1 (pure v) s
        Abstract.App t1 _ _ -> findExpectedDataType t1
        Abstract.Global v -> do
          (d, _ :: AbstractM) <- definition v
          return $ case d of
            DataDefinition _ -> Just v
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
  -> TCM (Vector (Plicitness, MetaP), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert typ = do
  typ' <- whnf typ
  prenexConvert' typ'

prenexConvert'
  :: Polytype
  -> TCM (Vector (Plicitness, MetaP), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert' (Abstract.Pi h p t resScope) = do
  y <- forall h p t
  let resType = Util.instantiate1 (pure y) resScope
  (vs, resType', f) <- prenexConvert resType
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
prenexConvert' typ = return (mempty, typ, pure)

--------------------------------------------------------------------------------
-- Subtyping/subsumption
-- | subtype t1 t2 = f => f : t1 -> t2
subtype :: Polytype -> Polytype -> TCM (AbstractM -> TCM AbstractM)
subtype typ1 typ2 = do
  logMeta 30 "subtype t1" typ1
  logMeta 30 "        t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtype' typ1' typ2'
  modifyIndent pred
  return res

subtype' :: Polytype -> Polytype -> TCM (AbstractM -> TCM AbstractM)
subtype' (Abstract.Pi h1 p1 argType1 retScope1) (Abstract.Pi h2 p2 argType2 retScope2)
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p2 argType2
    v1 <- f1 $ pure v2
    let retType1 = Util.instantiate1 v1 retScope1
        retType2 = Util.instantiate1 (pure v2) retScope2
    f2 <- subtype retType1 retType2
    return
      $ \x -> fmap (lam h p2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x p1 v1)
subtype' typ1 typ2 = do
  (as, rho, f1) <- prenexConvert typ2
  f2 <- subtypeRho typ1 rho $ InstBelow Explicit
  return $ \x ->
    f1 =<< lams <$> metaTelescopeM as
    <*> (abstractM (teleAbstraction $ snd <$> as) =<< f2 x)

subtypeRho :: Polytype -> Rhotype -> InstBelow -> TCM (AbstractM -> TCM AbstractM)
subtypeRho typ1 typ2 instBelow = do
  logMeta 30 "subtypeRho t1" typ1
  logMeta 30 "           t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtypeRho' typ1' typ2' instBelow
  modifyIndent pred
  return res

subtypeRho' :: Polytype -> Rhotype -> InstBelow -> TCM (AbstractM -> TCM AbstractM)
subtypeRho' typ1 typ2 _ | typ1 == typ2 = return pure
subtypeRho' (Abstract.Pi h1 p1 argType1 retScope1) (Abstract.Pi h2 p2 argType2 retScope2) _
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p2 argType2
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
  -> TCM
    ( Telescope Plicitness Abstract.ExprP MetaP
    , Scope Tele Abstract.ExprP MetaP
    , Vector (AbstractM -> TCM AbstractM)
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
        (argType, resScope, f) <- funSubtype typ p
        v <- forall mempty p argType
        go
          (Vector.tail ps)
          (Util.instantiate1 (pure v) resScope)
          (v : vs)
          ((mempty, p, argType) : tele)
          (f : fs)

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP MetaP, AbstractM -> TCM AbstractM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP MetaP, AbstractM -> TCM AbstractM)
funSubtype' (Abstract.Pi _ p t s) p' | p == p' = return (t, s, pure)
funSubtype' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtypeRho' (Abstract.Pi mempty p argType resScope) typ $ InstBelow p
  return (argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP MetaP, AbstractM -> TCM AbstractM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP MetaP, AbstractM -> TCM AbstractM)
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
  -> TCM (AbstractM, AbstractM)
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
  -> TCM (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c typ) = do
  typeType <- existsTypeType mempty
  typ' <- zonk =<< checkPoly typ typeType
  (sizes, ret) <- go typ'
  let size = foldr Builtin.AddSizeE (Abstract.Lit 0) sizes
  return (ConstrDef c typ', ret, size)
  where
    go :: AbstractM -> TCM ([AbstractM], AbstractM)
    go (Abstract.Pi h p t s) = do
      v <- forall h p t
      (sizes, ret) <- go $ instantiate1 (pure v) s
      size <- sizeOfType t
      return (size : sizes, ret)
    go ret = return ([], ret)

checkDataType
  :: MetaP
  -> DataDef Concrete.Expr MetaP
  -> AbstractM
  -> TCM (DataDef Abstract.ExprP MetaP, AbstractM)
checkDataType name (DataDef cs) typ = mdo
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  ps' <- forMTele (telescope typ') $ \h p s -> do
    let is = instantiateTele pure vs s
    v <- forall h p is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele pure vs t

  mapM_ (unify [] constrRetType) rets

  let addTagSize = case cs of
        [] -> id
        [_] -> id
        _ -> Builtin.AddSizeE $ Abstract.Lit 1

      typeSize = addTagSize
               $ foldr (Builtin.MaxSize Explicit Explicit) (Abstract.Lit 0) sizes

  let typeReturnType = Builtin.TypeP typeSize
  unify [] typeReturnType =<< typeOfM constrRetType

  abstractedReturnType <- abstractM abstr typeReturnType

  abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
    logMeta 20 ("checkDataType res " ++ show qc) e
    traverse (abstractM abstr) c

  params <- metaTelescopeM ps'
  let typ'' = pis params abstractedReturnType

  return (DataDef abstractedCs, typ'')

checkClauses
  :: NonEmpty (Concrete.Clause Concrete.Expr MetaP)
  -> Polytype
  -> TCM AbstractM
checkClauses clauses polyType = do

  -- TODO check plicitness of first pat before this?
  (vs, rhoType, f) <- prenexConvert polyType

  res <- checkClausesRho clauses rhoType

  f =<< lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) res

checkClausesRho
  :: NonEmpty (Concrete.Clause Concrete.Expr MetaP)
  -> Rhotype
  -> TCM AbstractM
checkClausesRho clauses rhoType = do
  forM_ clauses $ logMeta 20 "checkClausesRho clause"

  let ps = fst <$> pats
        where
          Concrete.Clause pats _ = NonEmpty.head clauses
  (argTele, returnTypeScope, fs) <- funSubtypes rhoType ps
  argVars <- mdo
    -- TODO get namehints from the patterns
    argVars <- forMTele argTele $ \h p s -> forall h p $ instantiateTele pure argVars s
    return argVars

  let returnType = instantiateTele pure argVars returnTypeScope

  modifyIndent succ

  clauses' <- forM clauses $ \(Concrete.Clause pats bodyScope) -> do
    (pats', patVars) <- checkPats (snd <$> pats) $ metaType <$> argVars
    logShow 20 "checkClausesRho clause patVars" patVars
    let body = instantiatePatternVec pure patVars bodyScope
    body' <- checkRho body returnType
    logMeta 20 "checkClausesRho clause body" body'
    return (pats', body')

  modifyIndent pred

  body <- matchClauses
    (Vector.toList $ pure <$> argVars)
    (NonEmpty.toList $ first Vector.toList <$> clauses')

  result <- foldrM
    (\(p, (f, v)) e ->
      f =<< Abstract.Lam (metaHint v) p (metaType v) <$> abstract1M v e)
    body
    (Vector.zip ps $ Vector.zip fs argVars)

  logMeta 20 "checkClauseRho res" result
  return result

checkDefType
  :: MetaP
  -> Concrete.PatDefinition Concrete.Expr MetaP
  -> SourceLoc
  -> AbstractM
  -> TCM (Definition Abstract.ExprP MetaP, AbstractM)
checkDefType v def loc typ = located (render loc) $ case def of
  Concrete.PatDefinition clauses -> do
    e' <- checkClauses clauses typ
    return (Definition e', typ)
  Concrete.PatDataDefinition d -> do
    (d', typ') <- checkDataType v d typ
    return (DataDefinition d', typ')

generaliseDef
  :: Vector MetaP
  -> Definition Abstract.ExprP MetaP
  -> AbstractM
  -> TCM ( Definition Abstract.ExprP MetaP
         , AbstractM
         )
generaliseDef vs (Definition e) t = do
  ge <- go lam e
  gt <- go pi_ t
  return (Definition ge, gt)
  where
    go c b = Foldable.foldrM
      (\a s -> c (metaHint a) Implicit (metaType a) <$> abstract1M a s)
      b
      vs
generaliseDef vs (DataDefinition (DataDef cs)) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  typ' <- foldrM (\v -> fmap (Abstract.Pi (metaHint v) Implicit (metaType v))
                      . abstract1M v) typ vs
  return (DataDefinition (DataDef cs'), typ')
  where
    f v = pure $ maybe (F v) (B . Tele) (v `Vector.elemIndex` vs)
    g = pure . B . (+ Tele (length vs))

generaliseDefs
  :: Vector ( MetaP
            , Definition Abstract.ExprP MetaP
            , AbstractM
            )
  -> TCM (Vector ( Definition Abstract.ExprP MetaP
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
    t' <- join      <$> traverse (sub instVars) t
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
  -> TCM (Vector ( Name
                 , Definition Abstract.ExprP Void
                 , Abstract.ExprP Void
                 )
         )
checkRecursiveDefs defs = do
  let names = (\(v, _, _, _) -> v) <$> defs

  (checkedDefs, evars) <- enterLevel $ do
    evars <- Vector.forM names $ \name -> do
      let hint = fromName name
      typ <- existsType hint
      forall hint Explicit (typ :: AbstractM)

    exposedDefs <- forM defs $ \(_, loc, def, typ) -> do
      let expose name = case Vector.elemIndex name names of
            Nothing -> global name
            Just index -> pure
              $ fromMaybe (error "checkRecursiveDefs 1")
              $ evars Vector.!? index
      return (loc, bound absurd expose def, bind absurd expose typ)

    checkedDefs <- forM (Vector.zip evars exposedDefs) $ \(evar, (loc, def, typ)) -> do
      typ' <- checkPoly typ =<< existsTypeType (metaHint evar)
      unify [] (metaType evar) typ'
      (def', typ'') <- checkDefType evar def loc typ'
      logMeta 20 ("checkRecursiveDefs res " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) def'
      logMeta 20 ("checkRecursiveDefs res t " ++ show (pretty $ fromJust $ unNameHint $ metaHint evar)) typ''
      return (evar, def', typ'')

    return (checkedDefs, evars)

  genDefs <- generaliseDefs checkedDefs

  forM (Vector.zip names genDefs) $ \(name, (def, typ)) -> do
    let unexpose evar = case Vector.elemIndex evar evars of
          Nothing -> pure evar
          Just index -> global
            $ fromMaybe (error "checkRecursiveDefs 2")
            $ names Vector.!? index
    let unexposedDef = bound unexpose global def
        unexposedTyp = bind unexpose global typ
        vf :: MetaP -> TCM b
        vf v = throwError $ "checkRecursiveDefs " ++ show v

    unexposedDef' <- traverse vf unexposedDef
    unexposedTyp' <- traverse vf unexposedTyp
    return (name, unexposedDef', unexposedTyp')
