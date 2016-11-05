{-# LANGUAGE OverloadedStrings, RecursiveDo, ScopedTypeVariables, TypeFamilies, ViewPatterns #-}
module Infer where

import Control.Monad.Except
import Control.Monad.ST()
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Foldable as F
import qualified Data.HashSet as HS
import Data.List as List
import Data.Maybe
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import Data.STRef
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Text.Trifecta.Result(Err(Err), explain)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen

import qualified Builtin
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

data Expected
  = Infer (STRef (World TCM) Rhotype) Plicitness
  | Check Rhotype

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected -> Polytype -> TCM (AbstractM -> TCM AbstractM)
instExpected (Check t2) t1 = subtype t1 t2
instExpected (Infer r maxPlicitness) t = do
  (t', f) <- instantiateForalls t maxPlicitness
  liftST $ writeSTRef r t'
  return f

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
checkPoly' expr@(Concrete.Lam _ Implicit _ _) polyType
  = checkRho expr polyType
checkPoly' expr polyType = do
  (vs, rhoType, f) <- prenexConvert polyType
  e <- checkRho expr rhoType
  logShow 25 "checkPoly: prenexConvert vars" vs
  f =<< lams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) e

inferPoly :: ConcreteM -> Plicitness -> TCM (AbstractM, Polytype)
inferPoly expr maxPlicitness = do
  logMeta 20 "inferPoly expr" expr
  modifyIndent succ
  (resExpr, resType) <- inferPoly' expr maxPlicitness
  modifyIndent pred
  logMeta 20 "inferPoly res expr" resExpr
  logMeta 20 "inferPoly res typ" resType
  return (resExpr, resType)

inferPoly' :: ConcreteM -> Plicitness -> TCM (AbstractM, Polytype)
inferPoly' expr maxPlicitness = do
  (expr', exprType) <- inferRho expr maxPlicitness
  generalise expr' exprType

instantiateForalls :: Polytype -> Plicitness -> TCM (Rhotype, AbstractM -> TCM AbstractM)
instantiateForalls typ maxPlicitness = do
  typ' <- whnf typ
  instantiateForalls' typ' maxPlicitness

instantiateForalls' :: Polytype -> Plicitness -> TCM (Rhotype, AbstractM -> TCM AbstractM)
instantiateForalls' (Abstract.Pi h p t s) maxPlicitness
  | p < maxPlicitness = do
    v <- exists h t
    let typ = instantiate1 (pure v) s
    (result, f) <- instantiateForalls typ maxPlicitness
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
checkRho' expr ty = tcRho expr (Check ty)

inferRho :: ConcreteM -> Plicitness -> TCM (AbstractM, Rhotype)
inferRho expr maxPlicitness = do
  logMeta 20 "inferRho" expr
  modifyIndent succ
  (resExpr, resType) <- inferRho' expr maxPlicitness
  modifyIndent pred
  logMeta 20 "inferRho res expr" resExpr
  logMeta 20 "inferRho res typ" resType
  return (resExpr, resType)

inferRho' :: ConcreteM -> Plicitness -> TCM (AbstractM, Rhotype)
inferRho' expr maxPlicitness = do
  ref <- liftST $ newSTRef $ error "inferRho: empty result"
  expr' <- tcRho expr $ Infer ref maxPlicitness
  typ <- liftST $ readSTRef ref
  return (expr', typ)

tcRho :: ConcreteM -> Expected -> TCM AbstractM
tcRho expr expected = case expr of
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
    typeName <- resolveConstrType [con] expected
    let qc = qualify typeName con
    typ <- qconstructor qc
    f <- instExpected expected typ
    f $ Abstract.Con qc
  Concrete.Pi h p varType scope -> do
    varType' <- checkPoly varType =<< existsTypeType h
    x <- forall h p varType'
    let body = instantiate1 (pure x) scope
    body' <- enterLevel $ checkPoly body =<< existsTypeType mempty
    f <- instExpected expected $ Builtin.TypeP $ Abstract.Lit 1
    f =<< Abstract.Pi h p varType' <$> abstract1M x body'
  Concrete.Lam h p varType bodyScope -> do
    varType' <- checkPoly varType =<< existsTypeType h
    case expected of
      Check expectedType -> do
        (argType, bodyTypeScope, fResult) <- funSubtype expectedType p
        fArg <- subtype argType varType'
        xArg <- forall h p argType
        xVar <- exists h varType'
        solve (fromJust $ metaRef xVar) =<< fArg (pure xArg)
        let body = instantiate1 (pure xVar) bodyScope
            bodyType = instantiate1 (pure xArg) bodyTypeScope
        body' <- enterLevel $ checkPoly body bodyType
        fResult =<< Abstract.Lam h p argType <$> abstract1M xArg body'
      Infer _ _ -> do
        x <- forall h p varType'
        let body = instantiate1 (pure x) bodyScope
        (body', bodyType) <- enterLevel $ inferRho body Explicit
        bodyScope' <- abstract1M x body'
        bodyTypeScope <- abstract1M x bodyType
        f <- instExpected expected $ Abstract.Pi h p varType' bodyTypeScope
        f $ Abstract.Lam h p varType' bodyScope'
  Concrete.App fun p arg -> do
    (fun', funType) <- inferRho fun p
    (argType, resTypeScope, f1) <- subtypeFun funType p
    case unusedScope resTypeScope of
      Nothing -> do
        arg' <- checkPoly arg argType
        let resType = instantiate1 arg' resTypeScope
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
  Concrete.SourceLoc loc e -> located loc $ tcRho e expected

tcBranches
  :: ConcreteM
  -> BranchesM (Either Constr QConstr) Plicitness Concrete.Expr
  -> Expected
  -> TCM AbstractM
tcBranches expr (ConBranches cbrs _) expected = do
  (expr', exprType) <- inferRho expr Explicit
  typeName <- resolveConstrType ((\(c, _, _) -> c) <$> cbrs) $ Check exprType
  (_dataType, params) <- instantiateDataType typeName

  instantiatedBranches <- forM cbrs $ \(c, tele, sbr) -> mdo
    args <- forMTele tele $ \h p s -> do
      let t = instantiateTele argVars s
      t' <- checkPoly t =<< existsTypeType mempty
      v <- forall h p t'
      return (p, pure v)
    let argVars = snd <$> args
    return (qualify typeName c, args, instantiateTele argVars sbr)

  inferredPatBranches <- forM instantiatedBranches $ \(qc, args, br) -> do
    paramsArgsExpr <- checkRho
      (apps (Concrete.Con $ Right qc) $ params <> args)
      exprType
    paramsArgsExpr' <- zonk paramsArgsExpr
    let (_, args') = appsView paramsArgsExpr'
        vs = Vector.fromList $ second fromVar <$> drop (Vector.length params) args'
        fromVar (Abstract.Var v) = v
        fromVar _ = error "inferBranches fromVar"
    return (qc, vs, br)

  (inferredBranches, resType) <- case expected of
    Check resType -> do
      brs <- forM inferredPatBranches $ \(qc, vs, br) -> do
        br' <- checkRho br resType
        return (qc, vs, br')
      return (brs, resType)
    Infer _ maxPlicitness -> do
      -- TODO Arm-less cases
      let (headQc, headVs, headBr) = head inferredPatBranches
      (headBr', resType) <- inferRho headBr maxPlicitness
      brs' <- forM (tail inferredPatBranches) $ \(qc, vs, br) -> do
        br' <- checkRho br resType
        return (qc, vs, br')
      return ((headQc, headVs, headBr'):brs', resType)

  cbrs' <- forM inferredBranches $ \(qc, vs, br) -> do
    sbr <- abstractM (teleAbstraction (snd <$> vs)) br
    tele <- Vector.forM vs $ \(p, v) -> do
      s <- abstractM (teleAbstraction (snd <$> vs)) $ metaType v
      return (metaHint v, p, s)
    return (qc, Telescope tele, sbr)

  f <- instExpected expected resType
  f $ Abstract.Case expr' $ ConBranches cbrs' resType
tcBranches expr (LitBranches lbrs d) expected = do
  expr' <- checkRho expr Builtin.Size
  (d', resType) <- case expected of
    Check resType -> do
      d' <- checkRho d resType
      return (d', resType)
    Infer _ maxPlicitness -> inferRho d maxPlicitness
  lbrs' <- forM lbrs $ \(l, e) -> do
    e' <- checkRho e resType
    return (l, e')
  f <- instExpected expected resType
  f $ Abstract.Case expr' $ LitBranches lbrs' d'

instantiateDataType
  :: Applicative f
  => Name
  -> TCM (AbstractM, Vector (Plicitness, f (MetaVar Abstract.ExprP)))
instantiateDataType typeName = mdo
  (_, dataTypeType) <- definition typeName
  let params = telescope dataTypeType
      inst = instantiateTele (pure . snd <$> paramVars)
  paramVars <- forMTele params $ \h p s -> do
    v <- exists h (inst s)
    return (p, v)
  let pureParamVars = fmap pure <$> paramVars
      dataType = apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (Implicit, pure v)) <$> paramVars
  return (dataType, implicitParamVars)

--------------------------------------------------------------------------------
-- Constrs
resolveConstrType
  :: [Either Constr QConstr]
  -> Expected
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
      Leijen.<+> prettyHumanList "and" (Leijen.dullgreen . pretty <$> xs)
      <> "."
      ]
  where
    expectedDataType =
      case expected of
        Infer _ _ -> return Nothing
        Check checkType -> do
          checkType' <- whnf checkType
          case appsView checkType' of
            (Abstract.Global v, _) -> do
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
  -> TCM (Vector (Plicitness, MetaVar Abstract.ExprP), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert typ = do
  typ' <- whnf typ
  prenexConvert' typ'

prenexConvert'
  :: Polytype
  -> TCM (Vector (Plicitness, MetaVar Abstract.ExprP), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert' (Abstract.Pi h p t resScope) = do
  y <- forall h p t
  let resType = instantiate1 (pure y) resScope
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
    let retType1 = instantiate1 v1 retScope1
        retType2 = instantiate1 (pure v2) retScope2
    f2 <- subtype retType1 retType2
    return
      $ \x -> fmap (lam h p2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x p1 v1)
subtype' typ1 typ2 = do
  (as, rho, f1) <- prenexConvert typ2
  f2 <- subtypeRho typ1 rho
  return $ \x ->
    f1 =<< lams <$> metaTelescopeM as
    <*> (abstractM (teleAbstraction $ snd <$> as) =<< f2 x)

subtypeRho :: Polytype -> Rhotype -> TCM (AbstractM -> TCM AbstractM)
subtypeRho typ1 typ2 = do
  logMeta 30 "subtypeRho t1" typ1
  logMeta 30 "           t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subtypeRho' typ1' typ2'
  modifyIndent pred
  return res

subtypeRho' :: Polytype -> Rhotype -> TCM (AbstractM -> TCM AbstractM)
subtypeRho' typ1 typ2 | typ1 == typ2 = return pure
subtypeRho' (Abstract.Pi h1 p1 argType1 retScope1) (Abstract.Pi h2 p2 argType2 retScope2)
  | p1 == p2 = do
    let h = h1 <> h2
    f1 <- subtype argType2 argType1
    v2 <- forall h p2 argType2
    v1 <- f1 $ pure v2
    let retType1 = instantiate1 v1 retScope1
        retType2 = instantiate1 (pure v2) retScope2
    f2 <- subtypeRho retType1 retType2
    return
      $ \x -> fmap (lam h p2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x p1 v1)
subtypeRho' (Abstract.Pi h Implicit t s) typ2 = do
  v <- exists h t
  f <- subtypeRho (instantiate1 (pure v) s) typ2
  return $ \x -> f $ Abstract.App x Implicit $ pure v
subtypeRho' typ1 typ2 = do
  unify [] typ1 typ2
  return pure

-- | funSubtype typ p = (typ1, typ2, f) => f : (typ1 -> typ2) -> typ
funSubtype
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM -> TCM AbstractM)
funSubtype typ p = do
  typ' <- whnf typ
  funSubtype' typ' p

funSubtype'
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM -> TCM AbstractM)
funSubtype' (Abstract.Pi _ p t s) p' | p == p' = return (t, s, pure)
funSubtype' typ p = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subtypeRho' (Abstract.Pi mempty p argType resScope) typ
  return (argType, resScope, f)

-- | subtypeFun typ p = (typ1, typ2, f) => f : typ -> (typ1 -> typ2)
subtypeFun
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM -> TCM AbstractM)
subtypeFun typ p = do
  typ' <- whnf typ
  subtypeFun' typ' p

subtypeFun'
  :: Rhotype
  -> Plicitness
  -> TCM (Rhotype, Scope1 Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM -> TCM AbstractM)
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
  fvs' <- HS.fromList <$> filterM p fvs

  deps <- forM (HS.toList fvs') $ \x -> do
    ds <- foldMapM HS.singleton $ metaType x
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
checkConstrDef (ConstrDef c (pisView -> (args, ret))) = mdo
  let inst = instantiateTele $ (\(a, _, _, _, _) -> pure a) <$> args'
  args' <- forMTele args $ \h p arg -> do
    argSize <- existsSize h
    arg' <- checkPoly (inst arg) $ Builtin.TypeP argSize
    v <- forall h p arg'
    return (v, h, p, arg', argSize)

  let sizes = (\(_, _, _, _, sz) -> sz) <$> args'
      size = foldr Builtin.AddSizeE (Abstract.Lit 0) sizes

  sizeVar <- existsSize mempty

  ret' <- checkPoly (inst ret) $ Builtin.TypeP sizeVar

  res <- F.foldrM (\(v, h, p, arg', _) rest ->
         Abstract.Pi h p arg' <$> abstract1M v rest) ret' args'
  return (ConstrDef c res, ret', size)

checkDataType
  :: MetaVar Abstract.ExprP
  -> DataDef Concrete.Expr (MetaVar Abstract.ExprP)
  -> AbstractM
  -> TCM (DataDef Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM)
checkDataType name (DataDef cs) typ = mdo
  typ' <- zonk typ
  logMeta 20 "checkDataType t" typ'

  ps' <- forMTele (telescope typ') $ \h p s -> do
    let is = instantiateTele (pure <$> vs) s
    v <- forall h p is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele (pure <$> vs) t

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

checkDefType
  :: MetaVar Abstract.ExprP
  -> Definition Concrete.Expr (MetaVar Abstract.ExprP)
  -> AbstractM
  -> TCM (Definition Abstract.ExprP (MetaVar Abstract.ExprP), AbstractM)
checkDefType _ (Definition e) typ = do
  e' <- checkPoly e typ
  return (Definition e', typ)
checkDefType v (DataDefinition d) typ = do
  (d', typ') <- checkDataType v d typ
  return (DataDefinition d', typ')

generaliseDef
  :: Vector (MetaVar Abstract.ExprP)
  -> Definition Abstract.ExprP (MetaVar Abstract.ExprP)
  -> AbstractM
  -> TCM ( Definition Abstract.ExprP (MetaVar Abstract.ExprP)
         , AbstractM
         )
generaliseDef vs (Definition e) t = do
  ge <- go lam e
  gt <- go pi_ t
  return (Definition ge, gt)
  where
    go c b = F.foldrM
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
  :: Vector ( MetaVar Abstract.ExprP
            , Definition Abstract.ExprP (MetaVar Abstract.ExprP)
            , AbstractM
            )
  -> TCM (Vector ( Definition Abstract.ExprP (Var Int (MetaVar Abstract.ExprP))
                 , ScopeM Int Abstract.ExprP
                 )
         )
generaliseDefs xs = do
  modifyIndent succ

  fvs <- asum <$> mapM (foldMapM (:[])) types

  l <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HS.fromList <$> filterM p fvs

  deps <- forM (HS.toList fvs') $ \x -> do
    ds <- foldMapM HS.singleton $ metaType x
    return (x, ds)

  let sortedFvs = map impure $ topoSort deps
      appl x = apps x [(Implicit, pure fv) | fv <- sortedFvs]
      instVars = appl . pure <$> vars

  instDefs <- forM xs $ \(_, d, t) -> do
    d' <- boundJoin <$> traverse (sub instVars) d
    t' <- join      <$> traverse (sub instVars) t
    return (d', t')

  genDefs <- mapM (uncurry $ generaliseDef $ Vector.fromList sortedFvs) instDefs
  abstrDefs <- mapM (uncurry $ abstractDefM (`Vector.elemIndex` vars)) genDefs

  modifyIndent pred

  return abstrDefs
  where
    vars  = (\(v, _, _) -> v) <$> xs
    types = (\(_, _, t) -> t) <$> xs
    sub instVars v | Just x <- v `Vector.elemIndex` vars = return $ instVars Vector.! x
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
            , Definition Concrete.Expr (Var Int (MetaVar Abstract.ExprP))
            , ScopeM Int Concrete.Expr
            )
  -> TCM (Vector ( Definition Abstract.ExprP (Var Int (MetaVar Abstract.ExprP))
                 , ScopeM Int Abstract.ExprP
                 )
         )
checkRecursiveDefs ds =
  generaliseDefs <=< enterLevel $ do
    evs <- Vector.forM ds $ \(v, _, _) -> do
      let h = fromText v
      t <- existsType h
      forall h Explicit (t :: AbstractM)
    let instantiatedDs = flip Vector.map ds $ \(_, e, t) ->
          ( instantiateDef (pure . (evs Vector.!)) e
          , instantiate (pure . (evs Vector.!)) t
          )
    flip Vector.imapM instantiatedDs $ \i (d, t) -> do
      let v = evs Vector.! i
      t' <- checkPoly t =<< existsTypeType mempty
      unify [] (metaType v) t'
      (d', t'') <- checkDefType v d t'
      logMeta 20 ("checkRecursiveDefs res " ++ show (metaHint v)) d'
      logMeta 20 ("checkRecursiveDefs res t " ++ show (metaHint v)) t'
      return (v, d', t'')
