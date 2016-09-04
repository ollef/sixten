{-# LANGUAGE RecursiveDo, OverloadedStrings, ViewPatterns #-}
module Infer where

import Control.Monad.Except
import Control.Monad.ST()
import Data.Bifunctor
import Data.Foldable as F
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

existsSize :: Monad e => NameHint -> TCM (e (MetaVar Abstract.Expr))
existsSize n = existsVar n Builtin.Size

existsType :: Monad e => NameHint -> TCM (e (MetaVar Abstract.Expr))
existsType n = do
  sz <- existsSize n
  t <- existsVar n $ Builtin.Type sz
  existsVar n t

data Generalise
  = Generalise
  | Instantiate
  deriving (Eq, Show)

checkType
  :: Relevance
  -> Plicitness -- ^ Used to eagerly instantiate applications in implicit contexts
  -> ConcreteM
  -> AbstractM
  -> TCM (AbstractM, AbstractM)
checkType surrR surrP expr typ = do
  tr ("checkType " ++ show (Annotation surrR surrP) ++ " e") expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Concrete.Con c@(Left _) -> do
      n <- resolveConstrType [c] $ Just typ
      checkType surrR surrP (Concrete.Con $ Right $ qualify n c) typ
    Concrete.App e1 a1 e2 -> do
      argType <- existsType mempty
      resType <- existsType mempty
      (e1', funType) <- checkType surrR surrP e1
        $ Abstract.Pi mempty a1 argType
        $ abstractNone resType
      case funType of
        Abstract.Pi h a2 argType' returnScope | plicitness a1 == plicitness a2
                                             && relevance a1 >= min (relevance a2) surrR -> do
          arg <- existsVar h argType'
          let returnType = instantiate1 arg returnScope
          (appResult, typ') <- subtype surrR surrP (Abstract.App e1' a2 arg) returnType typ
          (e2', _argType'') <- checkType (min (relevance a2) surrR) surrP e2 argType'
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
        (expr', typ') <- inferType surrR surrP expr
        subtype surrR surrP expr' typ' typ

inferType
  :: Relevance
  -> Plicitness
  -> ConcreteM
  -> TCM (AbstractM, AbstractM)
inferType surrR surrP expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Concrete.Global v -> do
      (_, typ) <- definition v
      return (Abstract.Global v, typ)
    Concrete.Var v -> return (Abstract.Var v, metaType v)
    Concrete.Con con -> do
      n <- resolveConstrType [con] Nothing
      let qc = qualify n con
      typ <- qconstructor qc
      return (Abstract.Con qc, typ)
    Concrete.Lit l -> return (Abstract.Lit l, Builtin.Size)
    Concrete.Pi n p t s -> do
      sz <- existsSize n
      (t', _) <- checkType Irrelevant surrP t $ Builtin.Type sz
      v  <- forall_ n t'
      (e', _) <- inferType Irrelevant surrP $ instantiate1 (pure v) s
      s' <- abstract1M v e'
      return (Abstract.Pi n p t' s', Builtin.Type $ Abstract.Lit 1)
    Concrete.Lam n p argType s -> {- uncurry generalise <=< enterLevel $ -} do
      sz <- existsSize n
      (argType', _) <- checkType Irrelevant surrP argType $ Builtin.Type sz
      x <- forall_ n argType'
      (e', resType) <- inferType surrR surrP $ instantiate1 (pure x) s
      s' <- abstract1M x e'
      abstractedResType <- abstract1M x resType
      return (Abstract.Lam n p argType' s', Abstract.Pi n p argType' abstractedResType)
    Concrete.App e1 a1 e2 -> do
      argType <- existsType mempty
      resType <- existsType mempty
      (e1', e1type) <- checkType surrR surrP e1
        $ Abstract.Pi mempty a1 argType
        $ abstractNone resType
      case e1type of
        Abstract.Pi _ a2 argType' resType' | plicitness a1 == plicitness a2
                                          && relevance a1 >= min (relevance a2) surrR -> do
          (e2', _) <- checkType (min (relevance a2) surrR) surrP e2 argType'
          return (Abstract.App e1' a2 e2', instantiate1 e2' resType')
        _ -> throwError "inferType: expected pi type"
    Concrete.Case e brs -> do
      (e'', brs', retType) <- inferBranches surrR surrP e brs
      return (Abstract.Case e'' brs', retType)
    Concrete.Anno e t  -> do
      (t', tType) <- inferType Irrelevant surrP t
      sz <- existsSize mempty
      (t'', _) <- subtype Irrelevant surrP t' tType $ Builtin.Type sz
      checkType surrR surrP e t''
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
  -> Maybe AbstractM
  -> TCM Name
resolveConstrType cs mtype = do
  n <- case mtype of
    -- TODO Also use a pi-view?
    Just (appsView -> (headType, _)) -> do
      headType' <- whnf headType
      case headType' of
        Abstract.Global v -> do
          (d, _) <- definition v
          return $ case d of
            DataDefinition _ -> [Set.singleton v]
            _                -> mempty
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

inferBranches
  :: Relevance
  -> Plicitness
  -> ConcreteM
  -> BranchesM (Either Constr QConstr) Concrete.Expr
  -> TCM ( AbstractM
         , BranchesM QConstr Abstract.Expr
         , AbstractM
         )
inferBranches surrR surrP expr (ConBranches cbrs _) = mdo
  (expr1, etype1) <- inferType surrR surrP expr

  tr "inferBranches e" expr1
  tr "              brs" $ ConBranches cbrs Concrete.Wildcard
  tr "              t" =<< freeze etype1
  modifyIndent succ

  typeName <- resolveConstrType ((\(c, _, _) -> c) <$> cbrs) $ Just etype1

  (_, dataTypeType) <- definition typeName
  let params = telescope dataTypeType
      inst = instantiateTele (pure . snd <$> paramVars)
  paramVars <- forMTele params $ \h p s -> do
    v <- exists h (inst s)
    return (p, v)

  let pureParamVars  = fmap pure <$> paramVars
      dataType = apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (IrIm, pure v)) <$> paramVars

  (expr2, etype2) <- subtype surrR surrP expr1 etype1 dataType

  let go (c, tele, sbr) (etype, resBrs, resType) = mdo
        args <- forMTele tele $ \h p s -> do
          let t = instantiateTele pureVs s
          sz <- existsSize h
          (t', _) <- checkType Irrelevant surrP t $ Builtin.Type sz
          v <- forall_ h t'
          return (p, pure v)
        let qc = qualify typeName c
            pureVs = snd <$> args
        (paramsArgsExpr, etype') <- checkType
          surrR surrP
          (Concrete.apps (Concrete.Con $ Right qc) $ implicitParamVars <> args)
          etype
        (br, resType') <- checkType surrR surrP (instantiateTele pureVs sbr) resType
        paramsArgsExpr' <- freeze paramsArgsExpr

        let (_, args') = appsView paramsArgsExpr'
            vs = V.fromList $ map (\(p, arg) -> (p, case arg of
                Abstract.Var v -> v
                _ -> error "inferBranches")) $ drop (teleLength params) args'
        sbr' <- abstractM (teleAbstraction (snd <$> vs)) br
        tele' <- V.forM vs $ \(p, v) -> do
          s <- abstractM (teleAbstraction (snd <$> vs)) $ metaType v
          return (metaHint v, p, s)
        return (etype', (qc, Telescope tele', sbr'):resBrs, resType')

  resType1 <- existsType mempty

  (etype3, cbrs2, resType2) <- foldrM go (etype2, mempty, resType1) cbrs

  (expr3, _etype3) <- subtype surrR surrP expr2 etype2 etype3

  modifyIndent pred
  tr "inferBranches res e" expr3
  tr "              res brs" $ ConBranches cbrs2 resType2
  tr "              res t" resType2
  return (expr3, ConBranches cbrs2 resType2, resType2)
inferBranches surrR surrP expr brs@(LitBranches lbrs d) = do
  tr "inferBranches e" expr
  tr "              brs" brs
  (expr', _etype') <- checkType surrR surrP expr Builtin.Size
  t <- existsType mempty
  lbrs' <- forM lbrs $ \(l, e) -> do
    (e', _) <- checkType surrR surrP e t
    return (l, e')
  (d', t') <- checkType surrR surrP d t
  -- let brs' = LitBranches lbrs' d'
  tr "inferBranches res e" =<< freeze expr'
  -- tr "              res brs" brs'
  tr "              res t" =<< freeze t'
  return (expr', LitBranches lbrs' d', t')

generalise
  :: AbstractM
  -> AbstractM
  -> TCM (AbstractM, AbstractM)
generalise expr typ = do
  tr "generalise e" expr
  tr "           t" typ
  modifyIndent succ

  -- fvs <- (<>) <$> foldMapM (:[]) typ <*> foldMapM (:[]) expr
  fvs <- foldMapM (:[]) typ -- <*> foldMapM (:[]) expr
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HS.fromList <$> filterM p fvs

  deps <- forM (HS.toList fvs') $ \x -> do
    ds <- foldMapM HS.singleton $ metaType x
    return (x, ds)

  let sorted = map go $ topoSort deps
  genexpr <- F.foldrM ($ etaLamM) expr sorted
  gentype <- F.foldrM ($ (\h a t s -> pure $ Abstract.Pi h a t s)) typ sorted

  modifyIndent pred
  tr "generalise res ge" genexpr
  tr "               gt" gentype
  return (genexpr, gentype)
  where
    go [a] f s = f (metaHint a) ReIm (metaType a) =<< abstract1M a s
    go _   _ _ = error "Generalise"

checkConstrDef
  :: ConstrDef ConcreteM
  -> TCM (ConstrDef AbstractM, AbstractM, AbstractM)
checkConstrDef (ConstrDef c (pisView -> (args, ret))) = mdo
  let inst = instantiateTele $ (\(a, _, _, _, _) -> pure a) <$> args'
  args' <- forMTele args $ \h a arg -> do
    argSize <- existsSize h
    (arg', _) <- checkType Irrelevant (plicitness a) (inst arg) $ Builtin.Type argSize
    v <- forall_ h arg'
    return (v, h, a, arg', argSize)

  let sizes = (\(_, _, _, _, sz) -> sz) <$> args'
      size = foldr Builtin.AddSize (Abstract.Lit 0) sizes

  sizeVar <- existsSize mempty

  (ret', _) <- checkType Irrelevant Explicit (inst ret) $ Builtin.Type sizeVar

  res <- F.foldrM (\(v, h, p, arg', _) rest ->
         Abstract.Pi h p arg' <$> abstract1M v rest) ret' args'
  return (ConstrDef c res, ret', size)

checkDataType
  :: MetaVar Abstract.Expr
  -> DataDef Concrete.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM ( DataDef Abstract.Expr (MetaVar Abstract.Expr)
         , AbstractM
         )
checkDataType name (DataDef cs) typ = mdo
  typ' <- freeze typ
  tr "checkDataType t" typ'

  ps' <- forMTele (telescope typ') $ \h p s -> do
    let is = instantiateTele (pure <$> vs) s
    v <- forall_ h is
    return (v, h, p, is)

  let vs = (\(v, _, _, _) -> v) <$> ps'
      constrRetType = apps (pure name) [(p, pure v) | (v, _, p, _) <- V.toList ps']

  params <- forM ps' $ \(_, h, p, t) -> (,,) h p <$> abstractM (fmap Tele . (`V.elemIndex` vs)) t

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

  abstractedReturnType <- abstractM (fmap Tele . (`V.elemIndex` vs)) typeReturnType
  let typ'' = pis (Telescope params) abstractedReturnType

  abstractedCs <- forM cs' $ \c ->
    traverse (abstractM (fmap Tele . (`V.elemIndex` vs))) c

  trp "dataDef" $ fmap (fmap show . fromScope) <$> abstractedCs
  tr "checkDataType res typ" typ''
  return (DataDef abstractedCs, typ'')

checkDefType
  :: MetaVar Abstract.Expr
  -> Definition Concrete.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM ( Definition Abstract.Expr (MetaVar Abstract.Expr)
         , AbstractM
         )
checkDefType _ (Definition e) typ = first Definition <$> checkType Relevant Explicit e typ
checkDefType v (DataDefinition d) typ = first DataDefinition <$> checkDataType v d typ

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
    f v = pure $ maybe (F v) (B . Tele) (v `V.elemIndex` vs)
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
  -- dfvs <- asum <$> mapM (foldMapM (:[])) defs

  l <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- HS.fromList <$> filterM p fvs
  -- dfvs' <- HS.fromList <$> filterM p dfvs
  trs "generaliseDefs l" l
  -- trs "generaliseDefs dfvs" dfvs
  -- trs "generaliseDefs dfvs'" dfvs'
  trs "generaliseDefs fvs" fvs
  trs "generaliseDefs fvs'" fvs'

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

  genDefs <- mapM (uncurry $ generaliseDef $ V.fromList sortedFvs) instDefs
  abstrDefs <- mapM (uncurry $ abstractDefM (`V.elemIndex` vars)) genDefs

  modifyIndent pred

  return abstrDefs
  where
    vars  = (\(v, _, _) -> v) <$> xs
    -- defs = (\(_, d, _) -> d) <$> xs
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
    evs <- V.forM ds $ \(v, _, _) -> do
      let h = fromText v
      t <- existsType h
      forall_ h t
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( instantiateDef (pure . (evs V.!)) e
          , instantiate (pure . (evs V.!)) t
          )
    sequence $ flip V.imap instantiatedDs $ \i (d, t) -> do
      let v = evs V.! i
      (t', _) <- inferType Irrelevant Explicit t
      unify (metaType v) t'
      (d', t'') <- checkDefType v d t'
      return (v, d', t'')
