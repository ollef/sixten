{-# LANGUAGE RecursiveDo, ViewPatterns #-}
module Typecheck where

import Control.Monad.Except
import Control.Monad.ST()
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Foldable as F
import qualified Data.HashSet as HS
import Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.STRef
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin
import Meta
import TCM
import Normalise
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import TopoSort
import Unify
import Util

type Polytype = AbstractM
type Monotype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

data Expected
  = Infer (STRef (World TCM) Polytype) Plicitness
  | Check Rhotype

--------------------------------------------------------------------------------
-- Rhotypes
checkRho :: ConcreteM -> Rhotype -> TCM AbstractM
checkRho expr typ = do
  tr "checkRho expr" expr
  tr "checkRho type" typ
  modifyIndent succ
  res <- checkRho' expr typ
  modifyIndent pred
  tr "checkRho res expr" res
  return res

checkRho' :: ConcreteM -> Rhotype -> TCM AbstractM
checkRho' expr ty = tcRho expr (Check ty)

inferRho :: ConcreteM -> Plicitness -> TCM (AbstractM, Rhotype)
inferRho expr maxPlicitness = do
  tr "inferRho" expr
  modifyIndent succ
  (resExpr, resType) <- inferRho' expr maxPlicitness
  modifyIndent pred
  tr "inferRho res expr" resExpr
  tr "inferRho res typ" resType
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
  Concrete.Pi h a varType scope -> do
    varType' <- checkPoly varType =<< existsTypeType h
    x <- forall h varType'
    let body = instantiate1 (pure x) scope
    body' <- enterLevel $ checkPoly body =<< existsTypeType mempty
    f <- instExpected expected $ Builtin.Type $ Abstract.Lit 1
    f =<< Abstract.Pi h a varType' <$> abstract1M x body'
  Concrete.Lam h a varType bodyScope -> do
    varType' <- checkPoly varType =<< existsTypeType h
    case expected of
      Check expectedType -> do
        (argType, bodyTypeScope, fResult) <- subsumesFun expectedType a
        fArg <- subsumption argType varType'
        xArg <- forall h argType
        xVar <- exists h varType'
        solve (fromJust $ metaRef xVar) =<< fArg (pure xArg)
        let body = instantiate1 (pure xVar) bodyScope
            bodyType = instantiate1 (pure xArg) bodyTypeScope
        body' <- enterLevel $ checkPoly body bodyType
        fResult =<< Abstract.Lam h a argType <$> abstract1M xArg body'
      Infer _ _ -> do
        x <- forall h varType'
        let body = instantiate1 (pure x) bodyScope
        (body', bodyType) <- enterLevel $ inferRho body Explicit
        bodyScope' <- abstract1M x body'
        bodyTypeScope <- abstract1M x bodyType
        f <- instExpected expected $ Abstract.Pi h a varType' bodyTypeScope
        f $ Abstract.Lam h a varType' bodyScope'
  Concrete.App fun a arg -> do
    (fun', funType) <- inferRho fun $ plicitness a
    (argType, resTypeScope, f1) <- subsumptionFun funType a
    arg' <- checkPoly arg argType
    let resType = instantiate1 arg' resTypeScope
    f2 <- instExpected expected resType
    fun'' <- f1 fun'
    f2 $ Abstract.App fun'' a arg'
  Concrete.Case e brs -> tcBranches e brs expected
  Concrete.Anno e t -> do
    t' <- checkPoly t =<< existsTypeType mempty
    e' <- checkPoly e t'
    f <- instExpected expected t'
    f e'
  Concrete.Wildcard -> do
    t <- existsType mempty
    f <- instExpected expected t
    x <- existsVar mempty t
    f x

-- | instExpected t2 t1 = e => e : t1 -> t2
instExpected :: Expected -> Polytype -> TCM (AbstractM -> TCM AbstractM)
instExpected (Check t2) t1 = subsumption t1 t2
instExpected (Infer r maxPlicitness) t = do
  (t', f) <- instantiateForalls t maxPlicitness
  liftST $ writeSTRef r t'
  return f

tcBranches
  :: ConcreteM
  -> BranchesM (Either Constr QConstr) Concrete.Expr
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
      v <- forall h t'
      return (p, pure v)
    let argVars = snd <$> args
    return (qualify typeName c, args, instantiateTele argVars sbr)

  inferredPatBranches <- forM instantiatedBranches $ \(qc, args, br) -> do
    paramsArgsExpr <- checkRho
      (Concrete.apps (Concrete.Con $ Right qc) $ params <> args)
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
  -> TCM (AbstractM, Vector (Annotation, f (MetaVar Abstract.Expr)))
instantiateDataType typeName = mdo
  (_, dataTypeType) <- definition typeName
  let params = telescope dataTypeType
      inst = instantiateTele (pure . snd <$> paramVars)
  paramVars <- forMTele params $ \h p s -> do
    v <- exists h (inst s)
    return (p, v)
  let pureParamVars  = fmap pure <$> paramVars
      dataType = apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (IrIm, pure v)) <$> paramVars
  return (dataType, implicitParamVars)

--------------------------------------------------------------------------------
-- Polytypes
checkPoly :: ConcreteM -> Polytype -> TCM AbstractM
checkPoly expr typ = do
  tr "checkPoly expr" expr
  tr "checkPoly type" typ
  modifyIndent succ
  res <- checkPoly' expr typ
  modifyIndent pred
  tr "checkPoly res expr" res
  return res

checkPoly' :: ConcreteM -> Polytype -> TCM AbstractM
checkPoly' expr@(Concrete.Lam _ (plicitness -> Implicit) _ _) polyType = do
  polyType' <- whnf polyType
  checkRho expr polyType'
checkPoly' expr polyType = do
  (vs, rhoType, f) <- prenexConvert polyType
  e <- checkRho expr rhoType
  trs "checkPoly: prenexConvert vars" vs
  f =<< Abstract.etaLams
    <$> metaTelescopeM vs
    <*> abstractM (teleAbstraction $ snd <$> vs) e

inferPoly :: ConcreteM -> Plicitness -> TCM (AbstractM, Polytype)
inferPoly expr maxPlicitness = do
  tr "inferPoly expr" expr
  modifyIndent succ
  (resExpr, resType) <- inferPoly' expr maxPlicitness
  modifyIndent pred
  tr "inferPoly res expr" resExpr
  tr "inferPoly res typ" resType
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
instantiateForalls' (Abstract.Pi h a t s) maxPlicitness
  | plicitness a < maxPlicitness = do
    v <- exists h t
    let typ = instantiate1 (pure v) s
    (result, f) <- instantiateForalls typ maxPlicitness
    return (result, \x -> f $ betaApp x a $ pure v)
instantiateForalls' typ _ = return (typ, pure)

--------------------------------------------------------------------------------
-- Constrs
resolveConstrType
  :: [Either Constr QConstr]
  -> Expected
  -> TCM Name
resolveConstrType cs expected = do
  n <- case expected of
    Check (appsView -> (headType, _)) -> do
      headType' <- whnf headType
      case headType' of
        Abstract.Global v -> do
          (d, _) <- definition v
          return $ case d of
            DataDefinition _ -> [Set.singleton v]
            _ -> mempty
        _ -> return mempty
    _ -> return mempty
  ns <- mapM (fmap (Set.map (fst :: (Name, Abstract.Expr ()) -> Name)) . constructor) cs
  case Set.toList $ List.foldl1' Set.intersection (n ++ ns) of
    [] -> case cs of
      [c] -> throwError $ "Not in scope: constructor " ++ show c ++ "."
      _ -> throwError $ "No type matching the constructors " ++ show cs ++ "."
    [x] -> return x
    xs -> throwError $ "Ambiguous constructors: " ++ show cs ++ ". Possible types: "
               ++ show xs ++ show (n ++ ns)

--------------------------------------------------------------------------------
-- Prenex conversion/deep skolemisation
-- | prenexConvert t1 = (vs, t2, f) => f : t2 -> t1
prenexConvert
  :: Polytype
  -> TCM (Vector (Annotation, MetaVar Abstract.Expr), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert typ = do
  typ' <- whnf typ
  prenexConvert' typ'

prenexConvert'
  :: Polytype
  -> TCM (Vector (Annotation, MetaVar Abstract.Expr), Rhotype, AbstractM -> TCM AbstractM)
prenexConvert' (Abstract.Pi h a t resScope) = do
  y <- forall h t
  let resType = instantiate1 (pure y) resScope
  (vs, resType', f) <- prenexConvert resType
  return $ case plicitness a of
    Implicit ->
      ( Vector.cons (a, y) vs
      , resType'
      , \x -> fmap (Abstract.etaLam h a t) $ abstract1M y
        =<< f (betaApp x a $ pure y)
      )
    Explicit ->
      ( vs
      , Abstract.Pi h a t $ abstract1 y resType'
      , \x -> fmap (Abstract.Lam h a t) . abstract1M y
        =<< f
        =<< Abstract.etaLams <$> metaTelescopeM vs
        <*> abstractM (teleAbstraction $ snd <$> vs)
        (betaApp (betaApps x $ second pure <$> vs) a $ pure y)
      )
prenexConvert' typ = return (mempty, typ, pure)

--------------------------------------------------------------------------------
-- Subsumption
subsumption :: Polytype -> Polytype -> TCM (AbstractM -> TCM AbstractM)
subsumption typ1 typ2 = do
  tr "subsumption t1" typ1
  tr "            t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subsumption' typ1' typ2'
  modifyIndent pred
  return res

subsumption' :: Polytype -> Polytype -> TCM (AbstractM -> TCM AbstractM)
subsumption' (Abstract.Pi h1 a1 argType1 retScope1) (Abstract.Pi h2 a2 argType2 retScope2)
  | plicitness a1 == plicitness a2 = do
    let h = h1 <> h2
    f1 <- subsumption argType2 argType1
    v2 <- forall h argType2
    v1 <- f1 $ pure v2
    let retType1 = instantiate1 v1 retScope1
        retType2 = instantiate1 (pure v2) retScope2
    f2 <- subsumption retType1 retType2
    return
      $ \x -> fmap (Abstract.etaLam h a2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x a1 v1)
subsumption' typ1 typ2 = do
  (as, rho, f1) <- prenexConvert typ2
  f2 <- subsumptionRho typ1 rho
  return $ \x ->
    f1 =<< Abstract.etaLams <$> metaTelescopeM as
    <*> (abstractM (teleAbstraction $ snd <$> as) =<< f2 x)

subsumptionRho :: Polytype -> Rhotype -> TCM (AbstractM -> TCM AbstractM)
subsumptionRho typ1 typ2 = do
  tr "subsumptionRho t1" typ1
  tr "               t2" typ2
  modifyIndent succ
  typ1' <- whnf typ1
  typ2' <- whnf typ2
  res <- subsumptionRho' typ1' typ2'
  modifyIndent pred
  return res

subsumptionRho' :: Polytype -> Rhotype -> TCM (AbstractM -> TCM AbstractM)
subsumptionRho' typ1 typ2 | typ1 == typ2 = return pure
subsumptionRho' (Abstract.Pi h1 a1 argType1 retScope1) (Abstract.Pi h2 a2 argType2 retScope2)
  | plicitness a1 == plicitness a2 = do
    let h = h1 <> h2
    f1 <- subsumption argType2 argType1
    v2 <- forall h argType2
    v1 <- f1 $ pure v2
    let retType1 = instantiate1 v1 retScope1
        retType2 = instantiate1 (pure v2) retScope2
    f2 <- subsumptionRho retType1 retType2
    return
      $ \x -> fmap (Abstract.etaLam h a2 argType2)
      $ abstract1M v2 =<< f2 (Abstract.App x a1 v1)
subsumptionRho' (Abstract.Pi h a t s) typ2
  | plicitness a == Implicit = do
    v <- exists h t
    f <- subsumptionRho (instantiate1 (pure v) s) typ2
    return $ \x -> f $ Abstract.App x a $ pure v
subsumptionRho' typ1 typ2 = do
  unify typ1 typ2
  return pure

subsumesFun
  :: Rhotype
  -> Annotation
  -> TCM (Rhotype, Scope1 Abstract.Expr (MetaVar Abstract.Expr), AbstractM -> TCM AbstractM)
subsumesFun typ a = do
  typ' <- whnf typ
  subsumptionFun' typ' a

subsumesFun'
  :: Rhotype
  -> Annotation
  -> TCM (Rhotype, Scope1 Abstract.Expr (MetaVar Abstract.Expr), AbstractM -> TCM AbstractM)
subsumesFun' (Abstract.Pi _ a t s) a' | a == a' = return (t, s, pure)
subsumesFun' typ a = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subsumptionRho' (Abstract.Pi mempty a argType resScope) typ
  return (argType, resScope, f)

subsumptionFun
  :: Rhotype
  -> Annotation
  -> TCM (Rhotype, Scope1 Abstract.Expr (MetaVar Abstract.Expr), AbstractM -> TCM AbstractM)
subsumptionFun typ a = do
  typ' <- whnf typ
  subsumptionFun' typ' a

subsumptionFun'
  :: Rhotype
  -> Annotation
  -> TCM (Rhotype, Scope1 Abstract.Expr (MetaVar Abstract.Expr), AbstractM -> TCM AbstractM)
subsumptionFun' (Abstract.Pi _ a t s) a' | a == a' = return (t, s, pure)
subsumptionFun' typ a = do
  argType <- existsType mempty
  resType <- existsType mempty
  let resScope = abstractNone resType
  f <- subsumption typ $ Abstract.Pi mempty a argType resScope
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
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HS.fromList <$> filterM p fvs

  deps <- forM (HS.toList fvs') $ \x -> do
    ds <- foldMapM HS.singleton $ metaType x
    return (x, ds)

  let sorted = map go $ topoSort deps
  genexpr <- foldrM ($ etaLamM) expr sorted
  gentype <- foldrM ($ (\h a t s -> pure $ Abstract.Pi h a t s)) typ sorted

  return (genexpr, gentype)
  where
    go [a] f s = f (metaHint a) ReIm (metaType a) =<< abstract1M a s
    go _   _ _ = error "Generalise"

--------------------------------------------------------------------------------
-- Definitions
checkConstrDef
  :: ConstrDef ConcreteM
  -> TCM (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c (pisView -> (args, ret))) = mdo
  let inst = instantiateTele $ (\(a, _, _, _, _) -> pure a) <$> args'
  args' <- forMTele args $ \h a arg -> do
    argSize <- existsSize h
    arg' <- checkPoly (inst arg) $ Builtin.Type argSize
    v <- forall h arg'
    return (v, h, a, arg', argSize)

  let sizes = (\(_, _, _, _, sz) -> sz) <$> args'
      size = foldr Builtin.AddSize (Abstract.Lit 0) sizes

  sizeVar <- existsSize mempty

  ret' <- checkPoly (inst ret) $ Builtin.Type sizeVar

  res <- F.foldrM (\(v, h, p, arg', _) rest ->
         Abstract.Pi h p arg' <$> abstract1M v rest) ret' args'
  return (ConstrDef c res, ret', size)

checkDataType
  :: MetaVar Abstract.Expr
  -> DataDef Concrete.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM (DataDef Abstract.Expr (MetaVar Abstract.Expr), AbstractM)
checkDataType name (DataDef cs) typ = mdo
  typ' <- zonk typ
  tr "checkDataType t" typ'

  ps' <- forMTele (telescope typ') $ \h p s -> do
    let is = instantiateTele (pure <$> vs) s
    v <- forall h is
    return (p, v)

  let vs = snd <$> ps'
      constrRetType = apps (pure name) $ second pure <$> ps'
      abstr = teleAbstraction vs

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) ->
    checkConstrDef $ ConstrDef c $ instantiateTele (pure <$> vs) t

  mapM_ (unify constrRetType) rets

  let addTagSize = case cs of
        [] -> id
        [_] -> id
        _ -> Builtin.AddSize $ Abstract.Lit 1

      typeSize = addTagSize
               $ foldr Builtin.MaxSize (Abstract.Lit 0) sizes

  let typeReturnType = Builtin.Type typeSize
  unify typeReturnType =<< typeOf constrRetType

  abstractedReturnType <- abstractM abstr typeReturnType

  abstractedCs <- forM cs' $ \c@(ConstrDef qc e) -> do
    tr ("checkDataType res " ++ show qc) e
    traverse (abstractM abstr) c

  params <- metaTelescopeM ps'
  let typ'' = pis params abstractedReturnType

  return (DataDef abstractedCs, typ'')

checkDefType
  :: MetaVar Abstract.Expr
  -> Definition Concrete.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM (Definition Abstract.Expr (MetaVar Abstract.Expr), AbstractM)
checkDefType _ (Definition e) typ = do
  e' <- checkPoly e typ
  return (Definition e', typ)
checkDefType v (DataDefinition d) typ = do
  (d', typ') <- checkDataType v d typ
  return (DataDefinition d', typ')

generaliseDef
  :: Vector (MetaVar Abstract.Expr)
  -> Definition Abstract.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM ( Definition Abstract.Expr (MetaVar Abstract.Expr)
         , AbstractM
         )
generaliseDef vs (Definition e) t = do
  ge <- go etaLamM e
  gt <- go (\h p typ s -> pure $ Abstract.Pi h p typ s) t
  return (Definition ge, gt)
  where
    go c b = F.foldrM
      (\a s -> c (metaHint a) ReIm (metaType a)
            =<< abstract1M a s)
      b
      vs
generaliseDef vs (DataDefinition (DataDef cs)) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  typ' <- foldrM (\v -> fmap (Abstract.Pi (metaHint v) ReIm (metaType v))
                      . abstract1M v) typ vs
  return (DataDefinition (DataDef cs'), typ')
  where
    f v = pure $ maybe (F v) (B . Tele) (v `Vector.elemIndex` vs)
    g = pure . B . (+ Tele (length vs))

generaliseDefs
  :: Vector ( MetaVar Abstract.Expr
            , Definition Abstract.Expr (MetaVar Abstract.Expr)
            , AbstractM
            )
  -> TCM (Vector ( Definition Abstract.Expr (Var Int (MetaVar Abstract.Expr))
                 , ScopeM Int Abstract.Expr
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
      appl x = apps x [(ReIm, pure fv) | fv <- sortedFvs]
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
            , Definition Concrete.Expr (Var Int (MetaVar Abstract.Expr))
            , ScopeM Int Concrete.Expr
            )
  -> TCM (Vector ( Definition Abstract.Expr (Var Int (MetaVar Abstract.Expr))
                 , ScopeM Int Abstract.Expr
                 )
         )
checkRecursiveDefs ds =
  generaliseDefs <=< enterLevel $ do
    evs <- Vector.forM ds $ \(v, _, _) -> do
      let h = fromText v
      t <- existsType h
      forall h t
    let instantiatedDs = flip Vector.map ds $ \(_, e, t) ->
          ( instantiateDef (pure . (evs Vector.!)) e
          , instantiate (pure . (evs Vector.!)) t
          )
    sequence $ flip Vector.imap instantiatedDs $ \i (d, t) -> do
      let v = evs Vector.! i
      t' <- checkPoly t =<< existsTypeType mempty
      unify (metaType v) t'
      (d', t'') <- checkDefType v d t'
      tr ("checkRecursiveDefs res " ++ show (metaHint v)) d'
      tr ("checkRecursiveDefs res t " ++ show (metaHint v)) t'
      return (v, d', t'')
