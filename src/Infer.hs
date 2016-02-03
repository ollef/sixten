{-# LANGUAGE RecursiveDo, ViewPatterns #-}
module Infer where

import Control.Monad.Except
import Control.Monad.ST()
import Data.Bifunctor
import Data.Foldable as F
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List as List
import Data.Monoid
import qualified Data.Set as Set
import Data.Vector(Vector)
import qualified Data.Vector as V

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

checkType
  :: Plicitness
  -> ConcreteM s
  -> AbstractM s
  -> TCM s (AbstractM s, AbstractM s)
checkType surrounding expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Concrete.Con c@(Left _) -> do
      n <- resolveConstrType [c] typ
      checkType surrounding (Concrete.Con $ Right $ qualify n c) typ
    Concrete.Lam m p s -> do
      typ' <- whnf typ
      case typ' of
        Abstract.Pi h p' a ts | p == p' -> do
          v <- forall_ (h <> m) a
          (body, ts') <- checkType surrounding
                                   (instantiate1 (pure v) s)
                                   (instantiate1 (pure v) ts)
          expr' <- Abstract.Lam (m <> h) p a <$> abstract1M v body
          typ'' <- Abstract.Pi  (h <> m) p a <$> abstract1M v ts'
          return (expr', typ'')
        Abstract.Pi h p' a ts | p' == Implicit || surrounding == Implicit -> do
          v <- forall_ h a
          (expr', ts') <- checkType surrounding expr (instantiate1 (pure v) ts)
          expr'' <- etaLamM h p' a =<< abstract1M v expr'
          typ''  <- Abstract.Pi  h p' a <$> abstract1M v ts'
          return (expr'', typ'')
        _ -> inferIt
    Concrete.App e1 p e2 -> do
      argType <- existsType mempty
      resType <- existsType mempty
      (e1', funType) <- checkType surrounding e1 $ Abstract.Pi mempty p argType
                                                 $ abstractNone resType
      case funType of
        Abstract.Pi h p' argType' returnScope | p == p' -> do
          arg <- existsVar h argType'
          let returnType = instantiate1 arg returnScope
          (appResult, typ') <- subtype surrounding (Abstract.App e1' p arg) returnType typ
          (e2', _argType'') <- checkType surrounding e2 argType'
          unify e2' arg
          return (appResult, typ')
        _ -> throwError "checkType: expected pi type"
    _ -> inferIt
  modifyIndent pred
  tr "checkType res e" =<< freeze rese
  tr "              t" =<< freeze rest
  return (rese, rest)
    where
      inferIt = do
        (expr', typ') <- inferType surrounding expr
        subtype surrounding expr' typ' typ

existsTypeType :: NameHint -> TCM s (AbstractM s)
existsTypeType n = do
  sz <- existsVar n Builtin.sizeE
  existsVar n (Builtin.typeE sz)

existsType :: NameHint -> TCM s (AbstractM s)
existsType n = do
  t <- existsTypeType n
  existsVar n t

inferType
  :: Plicitness
  -> ConcreteM s
  -> TCM s (AbstractM s, AbstractM s)
inferType surrounding expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Concrete.Global v -> do
      (_, typ) <- context v
      return (Abstract.Global v, typ)
    Concrete.Var v -> return (Abstract.Var v, metaType v)
    Concrete.Con con -> do
      n <- resolveConstrType [con] (Abstract.Global Builtin.type_)
      let qc = qualify n con
      typ <- qconstructor qc
      return (Abstract.Con qc, typ)
    Concrete.Lit l -> return (Abstract.Lit l, Builtin.sizeE)
    Concrete.Pi n p t s -> do
      argTypeType <- existsTypeType n
      (t', _) <- checkType p t argTypeType
      v  <- forall_ n t'
      resTypeType <- existsTypeType mempty
      (e', _) <- checkType surrounding (instantiate1 (pure v) s) resTypeType
      s' <- abstract1M v e'
      return (Abstract.Pi n p t' s', Builtin.typeN 1)
    Concrete.Lam n p s -> uncurry generalise <=< enterLevel $ do
      argType <- existsType n
      resType <- existsType mempty
      x <- forall_ n argType
      (e', resType')  <- checkType surrounding (instantiate1 (pure x) s) resType
      s' <- abstract1M x e'
      abstractedResType <- abstract1M x resType'
      return (Abstract.Lam n p argType s', Abstract.Pi n p argType abstractedResType)
    Concrete.App e1 p e2 -> do
      argType <- existsType mempty
      resType <- existsType mempty
      (e1', e1type) <- checkType surrounding e1 $ Abstract.Pi mempty p argType
                                                $ abstractNone resType
      case e1type of
        Abstract.Pi _ p' argType' resType' | p == p' -> do
          (e2', _) <- checkType p e2 argType'
          return (Abstract.App e1' p e2', instantiate1 e2' resType')
        _ -> throwError "inferType: expected pi type"
    Concrete.Case e brs -> do
      (e'', brs', retType) <- inferBranches surrounding e brs
      return (Abstract.Case e'' brs', retType)
    Concrete.Anno e t  -> do
      tType <- existsTypeType mempty
      (t', _) <- checkType surrounding t tType
      checkType surrounding e t'
    Concrete.Wildcard  -> do
      t <- existsType mempty
      x <- existsVar mempty t
      return (x, t)
  modifyIndent pred
  tr "inferType res e" =<< freeze e
  tr "              t" =<< freeze t
  return (e, t)

resolveConstrType
  :: [Either Constr QConstr]
  -> AbstractM s
  -> TCM s Name
resolveConstrType cs (Abstract.appsView -> (headType, _)) = do
  headType' <- whnf headType
  n <- case headType' of
    Abstract.Global v | v /= Builtin.type_ -> do
      (d, _) <- context v
      case d of
        DataDefinition _ -> return [Set.singleton v]
        _                -> return mempty
    _ -> return mempty
  ns <- mapM (fmap (Set.map (fst :: (Name, Abstract.Expr ()) -> Name)) . constructor) cs
  case Set.toList $ List.foldl1' Set.intersection (n ++ ns) of
    [x] -> return x
    xs -> throwError $ "Ambiguous constructors: " ++ show cs ++ ". Possible types: "
               ++ show xs ++ show (n ++ ns)

inferBranches
  :: Plicitness
  -> ConcreteM s
  -> BranchesM (Either Constr QConstr) Concrete.Expr s
  -> TCM s ( AbstractM s
           , BranchesM QConstr Abstract.Expr s
           , AbstractM s
           )
inferBranches surrounding expr (ConBranches cbrs _) = mdo
  (expr1, etype1) <- inferType surrounding expr

  tr "inferBranches e" expr1
  tr "              brs" $ ConBranches cbrs Concrete.Wildcard
  tr "              t" =<< freeze etype1
  modifyIndent succ

  typeName <- resolveConstrType ((\(c, _, _) -> c) <$> cbrs) etype1

  (_, dataTypeType) <- context typeName
  let (params, _) = bindingsView Abstract.piView dataTypeType
      inst = instantiateTele (pure . snd <$> paramVars)
  paramVars <- forTele params $ \h p s -> do
    v <- exists h (inst s)
    return (p, v)

  let pureParamVars  = fmap pure <$> paramVars
      dataType = Abstract.apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (Implicit, pure v)) <$> paramVars

  (expr2, etype2) <- subtype surrounding expr1 etype1 dataType

  let go (c, nps, sbr) (etype, resBrs, resType) = do
        args <- V.forM nps $ \(h, p) -> do
          t <- existsType h
          v <- forall_ h t
          return (p, pure v)
        let qc = qualify typeName c
            pureVs = snd <$> args
        (paramsArgsExpr, etype') <- checkType
          surrounding
          (Concrete.apps (Concrete.Con $ Right qc) $ implicitParamVars <> args)
          etype
        (br, resType') <- checkType surrounding (instantiateTele pureVs sbr) resType
        paramsArgsExpr' <- freeze paramsArgsExpr

        let (_, args') = Abstract.appsView paramsArgsExpr'
            vs = V.fromList $ map (\(p, arg) -> (p, case arg of
                Abstract.Var v -> Just v
                _ -> Nothing)) $ drop (teleLength params) args'
        sbr' <- abstractM (teleAbstraction (snd <$> vs) . Just) br
        let nps' = (\(p, mv) -> (maybe (Hint Nothing) metaHint mv, p)) <$> vs
        return (etype', (qc, nps', sbr'):resBrs, resType')

  resType1 <- existsType mempty

  (etype3, cbrs2, resType2) <- foldrM go (etype2, mempty, resType1) cbrs

  (expr3, _etype3) <- subtype surrounding expr2 etype2 etype3

  modifyIndent pred
  tr "inferBranches res e" expr3
  tr "              res brs" $ ConBranches cbrs2 resType2
  tr "              res t" resType2
  return (expr3, ConBranches cbrs2 resType2, resType2)
inferBranches surrounding expr brs@(LitBranches lbrs d) = do
  tr "inferBranches e" expr
  tr "              brs" brs
  (expr', _etype') <- checkType surrounding expr Builtin.sizeE
  t <- existsType mempty
  lbrs' <- forM lbrs $ \(l, e) -> do
    (e', _) <- checkType surrounding e t
    return (l, e')
  (d', t') <- checkType surrounding d t
  -- let brs' = LitBranches lbrs' d'
  tr "inferBranches res e" =<< freeze expr'
  -- tr "              res brs" brs'
  tr "              res t" =<< freeze t'
  return (expr', LitBranches lbrs' d', t')

generalise
  :: AbstractM s
  -> AbstractM s
  -> TCM s (AbstractM s, AbstractM s)
generalise expr typ = do
  tr "generalise e" expr
  tr "           t" typ
  modifyIndent succ

  fvs <- foldMapM (:[]) typ
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- filterM p fvs

  deps <- HM.fromList <$> forM fvs' (\x -> do
    ds <- foldMapM HS.singleton $ metaType x
    return (x, ds)
   )
  let sorted = map go $ topoSort deps
  genexpr <- F.foldrM ($ etaLamM) expr sorted
  gentype <- F.foldrM ($ (\h d t s -> pure $ Abstract.Pi h d t s)) typ sorted

  modifyIndent pred
  tr "generalise res ge" genexpr
  tr "               gt" gentype
  return (genexpr, gentype)
  where
    go [a] f s = f (metaHint a) Implicit (metaType a) =<< abstract1M a s
    go _   _ _ = error "Generalise"

checkConstrDef
  :: ConstrDef (ConcreteM s)
  -> TCM s (ConstrDef (AbstractM s), AbstractM s, AbstractM s)
checkConstrDef (ConstrDef c (bindingsView Concrete.piView -> (args, ret))) = mdo
  let inst = instantiateTele $ (\(a, _, _, _, _) -> pure a) <$> args'
  args' <- forTele args $ \h p arg -> do
    argSize <- existsVar h Builtin.sizeE
    (arg', _) <- checkType p (inst arg) $ Builtin.typeE argSize
    v <- forall_ h arg'
    return (v, h, p, arg', argSize)

  let sizes = (\(_, _, _, _, sz) -> sz) <$> args'
      size = foldr Builtin.addSizeE (Abstract.Lit 0) sizes

  sizeVar <- existsVar mempty Builtin.sizeE

  (ret', _) <- checkType Explicit (inst ret) $ Builtin.typeE sizeVar

  res <- F.foldrM (\(v, h, p, arg', _) rest ->
         Abstract.Pi h p arg' <$> abstract1M v rest) ret' args'
  return (ConstrDef c res, ret', size)

checkDataType
  :: MetaVar s
  -> DataDef Concrete.Expr (MetaVar s)
  -> AbstractM s
  -> TCM s ( DataDef Abstract.Expr (MetaVar s)
           , AbstractM s
           )
checkDataType name (DataDef cs) typ = mdo
  typ' <- freeze typ
  tr "checkDataType t" typ'

  ps' <- forTele (Abstract.telescope typ') $ \h p s -> do
    let is = instantiateTele (pure <$> vs) s
    v <- forall_ h is
    return (v, h, p, is)

  let vs = (\(v, _, _, _) -> v) <$> ps'
      constrRetType = Abstract.apps (pure name) [(p, pure v) | (v, _, p, _) <- V.toList ps']

  params <- forM ps' $ \(_, h, p, t) -> (,,) h p <$> abstractM (fmap Tele . (`V.elemIndex` vs)) t

  (cs', rets, sizes) <- fmap unzip3 $ forM cs $ \(ConstrDef c t) -> do
    (res, ret, size) <- checkConstrDef (ConstrDef c $ instantiateTele (pure <$> vs) t)
    ares <- traverse (abstractM (fmap Tele . (`V.elemIndex` vs))) res
    return (ares, ret, size)

  mapM_ (unify constrRetType) rets

  let typSize = Builtin.addSizeE (Abstract.Lit 1)
              $ foldr Builtin.maxSizeE (Abstract.Lit 0) sizes

      typeReturnType = Builtin.typeE typSize
      typ'' = quantify Abstract.Pi (abstractNone typeReturnType) $ Telescope params

  unify typeReturnType =<< typeOf constrRetType

  tr "checkDataType res typ" typ''
  return (DataDef cs', typ'')

checkDefType
  :: MetaVar s
  -> Definition Concrete.Expr (MetaVar s)
  -> AbstractM s
  -> TCM s ( Definition Abstract.Expr (MetaVar s)
           , AbstractM s
           )
checkDefType _ (Definition e) typ = first Definition <$> checkType Explicit e typ
checkDefType v (DataDefinition d) typ = first DataDefinition <$> checkDataType v d typ

generaliseDef
  :: Vector (MetaVar s)
  -> Definition Abstract.Expr (MetaVar s)
  -> AbstractM s
  -> TCM s ( Definition Abstract.Expr (MetaVar s)
           , AbstractM s
           )
generaliseDef vs (Definition e) t = do
  ge <- go etaLamM e
  gt <- go (\h p typ s -> pure $ Abstract.Pi h p typ s) t
  return (Definition ge, gt)
  where
    go c b = F.foldrM
      (\a s -> c (metaHint a) Implicit (metaType a)
            =<< abstract1M a s)
      b
      vs
generaliseDef vs (DataDefinition (DataDef cs)) typ = do
  let cs' = map (fmap $ toScope . splat f g) cs
  -- Abstract vs on top of typ
  typ' <- foldrM (\v -> fmap (Abstract.Pi (metaHint v) Implicit (metaType v))
                      . abstract1M v) typ vs
  return (DataDefinition (DataDef cs'), typ')
  where
    f v = pure $ maybe (F v) (B . Tele) (v `V.elemIndex` vs)
    g = pure . B . (+ Tele (length vs))

generaliseDefs
  :: Vector ( MetaVar s
            , Definition Abstract.Expr (MetaVar s)
            , AbstractM s
            )
  -> TCM s (Vector ( Definition Abstract.Expr (Var Int (MetaVar s))
                   , ScopeM Int Abstract.Expr s
                   )
           )
generaliseDefs xs = do
  modifyIndent succ
  -- trs "generaliseDefs xs" xs

  fvs <- asum <$> mapM (foldMapM (:[])) types
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- filterM p fvs
  -- trs "generaliseDefs l" l
  -- trs "generaliseDefs vs" fvs'

  deps <- HM.fromList <$> forM fvs' (\x -> do
    ds <- foldMapM HS.singleton $ metaType x
    return (x, ds)
   )
  let sortedFvs = map impure $ topoSort deps
      appl x = Abstract.apps x [(Implicit, pure fv) | fv <- sortedFvs]
      instVars = appl . pure <$> vars

  instDefs <- forM xs $ \(_, d, t) -> do
    d' <- boundJoin <$> traverse (sub instVars) d
    t' <- join      <$> traverse (sub instVars) t
    return (d', t')

  genDefs <- mapM (uncurry $ generaliseDef $ V.fromList sortedFvs) instDefs
  abstrDefs <- mapM (uncurry $ abstractDefM (`V.elemIndex` vars)) genDefs

  modifyIndent pred

  return abstrDefs
  where
    vars  = (\(v, _, _) -> v) <$> xs
    types = (\(_, _, t) -> t) <$> xs
    sub instVars v | Just x <- v `V.elemIndex` vars = return $ instVars V.! x
    sub instVars v@(metaRef -> Just r) = do
      sol <- solution r
      case sol of
        Left _ -> return $ pure v
        Right s -> join <$> traverse (sub instVars) s
    sub _ v = return $ pure v
    impure [a] = a
    impure _ = error "generaliseDefs"

checkRecursiveDefs
  :: Vector ( NameHint
            , Definition Concrete.Expr (Var Int (MetaVar s))
            , ScopeM Int Concrete.Expr s
            )
  -> TCM s (Vector ( Definition Abstract.Expr (Var Int (MetaVar s))
                   , ScopeM Int Abstract.Expr s
                   )
           )
checkRecursiveDefs ds =
  generaliseDefs <=< enterLevel $ do
    evs <- V.forM ds $ \(v, _, _) -> do
      t <- existsType v
      forall_ v t
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( instantiateDef (pure . (evs V.!)) e
          , instantiate (pure . (evs V.!)) t
          )
    sequence $ flip V.imap instantiatedDs $ \i (d, t) -> do
      let v = evs V.! i
      (t', _) <- inferType Explicit t
      unify (metaType v) t'
      (d', t'') <- checkDefType v d t'
      return (v, d', t'')
