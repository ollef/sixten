{-# LANGUAGE RecursiveDo, ViewPatterns #-}
module Infer where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.ST()
import Data.Bifunctor
import Data.Foldable as F
import Data.List as List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
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
  -> Concrete s
  -> Abstract s
  -> TCM s (Abstract s, Abstract s)
checkType surrounding expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Concrete.Con c@(Left _) -> do
      n <- resolveConstrType [c] typ
      checkType surrounding (Concrete.Con $ Right $ qualify n c) typ
    Concrete.Lam m p s -> do
      typ' <- whnf mempty plicitness typ
      case typ' of
        Abstract.Pi h p' a ts | p == p' -> do
          v <- forall_ (h <> m) a ()
          (body, ts') <- checkType surrounding
                                   (instantiate1 (pure v) s)
                                   (instantiate1 (pure v) ts)
          expr' <- Abstract.Lam (m <> h) p a <$> abstract1M v body
          typ'' <- Abstract.Pi  (h <> m) p a <$> abstract1M v ts'
          return (expr', typ'')
        Abstract.Pi h p' a ts | p' == Implicit -> do
          v <- forall_ h a ()
          (expr', ts') <- checkType surrounding expr (instantiate1 (pure v) ts)
          expr'' <- etaLamM h p' a =<< abstract1M v expr'
          typ''  <- Abstract.Pi  h p' a <$> abstract1M v ts'
          return (expr'', typ'')
        _ -> inferIt
    _ -> inferIt
  modifyIndent pred
  tr "checkType res e" =<< freeze rese
  tr "              t" =<< freeze rest
  return (rese, rest)
    where
      inferIt = do
        (expr', typ') <- inferType surrounding expr
        subtype surrounding expr' typ' typ

inferType
  :: Plicitness
  -> Concrete s
  -> TCM s (Abstract s, Abstract s)
inferType surrounding expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Concrete.Global v -> do
      (_, typ, _) <- context v
      return (Abstract.Global v, first plicitness typ)
    Concrete.Var v -> return (Abstract.Var v, metaType v)
    Concrete.Con con -> do
      n <- resolveConstrType [con] Abstract.Type
      let qc = qualify n con
      typ <- qconstructor qc
      return (Abstract.Con qc, first plicitness typ)
    Concrete.Lit l -> return (Abstract.Lit l, Builtin.int)
    Concrete.Type -> return (Abstract.Type, Abstract.Type)
    Concrete.Pi n p t s -> do
      (t', _) <- checkType p t Abstract.Type
      v  <- forall_ n t' ()
      (e', _) <- checkType surrounding (instantiate1 (pure v) s) Abstract.Type
      s' <- abstract1M v e'
      return (Abstract.Pi n p t' s', Abstract.Type)
    Concrete.Lam n p s -> uncurry generalise <=< enterLevel $ do
      atype <- existsVar n Abstract.Type ()
      a <- existsVar n atype ()
      b <- existsVar mempty Abstract.Type ()
      x <- forall_ n a ()
      (e', b')  <- checkType surrounding (instantiate1 (pure x) s) b
      s' <- abstract1M x e'
      ab <- abstract1M x b'
      return (Abstract.Lam n p a s', Abstract.Pi n p a ab)
    Concrete.App e1 p e2 -> do
      a <- existsVar mempty Abstract.Type ()
      b <- existsVar mempty Abstract.Type ()
      (e1', e1type) <- checkType surrounding e1 $ Abstract.Pi mempty p a
                                                $ abstractNone b
      case e1type of
        Abstract.Pi _ p' a' b' | p == p' -> do
          (e2', _) <- checkType p e2 a'
          return (Abstract.App e1' p e2', instantiate1 e2' b')
        _ -> throwError "inferType: expected pi type"
    Concrete.Case e brs -> do
      (e'', brs', retType) <- inferBranches surrounding e brs
      return (Abstract.Case e'' brs', retType)
    Concrete.Anno e t  -> do
      (t', _) <- checkType surrounding t Abstract.Type
      checkType surrounding e t'
    Concrete.Wildcard  -> do
      t <- existsVar mempty Abstract.Type ()
      x <- existsVar mempty t ()
      return (x, t)
  modifyIndent pred
  tr "inferType res e" =<< freeze e
  tr "              t" =<< freeze t
  return (e, t)

resolveConstrType
  :: [Either Constr QConstr]
  -> Abstract s
  -> TCM s Name
resolveConstrType cs (Abstract.appsView -> (headType, _)) = do
  headType' <- whnf mempty plicitness headType
  n <- case headType' of
    Abstract.Global v -> do
      (d, _, _) <- context v
      case d of
        DataDefinition _ -> return [Set.singleton v]
        _                -> return mempty
    _ -> return mempty
  ns <- mapM (fmap (Set.map (fst :: (Name, Abstract.Expr Annotation ()) -> Name)) . constructor) cs
  case Set.toList $ List.foldl1' Set.intersection (n ++ ns) of
    [x] -> return x
    xs -> throwError $ "Ambiguous constructors: " ++ show cs ++ ". Possible types: "
               ++ show xs

inferBranches
  :: Plicitness
  -> Concrete s
  -> BranchesM (Either Constr QConstr) Concrete.Expr s () Plicitness
  -> TCM s ( Abstract s
           , BranchesM QConstr (Abstract.Expr Plicitness) s () Plicitness
           , Abstract s
           )
inferBranches surrounding expr (ConBranches cbrs) = mdo
  (expr1, etype1) <- inferType surrounding expr

  tr "inferBranches e" expr1
  tr "              brs" $ ConBranches cbrs
  tr "              t" =<< freeze etype1
  modifyIndent succ

  typeName <- resolveConstrType ((\(c, _, _) -> c) <$> cbrs) etype1

  (_, dataTypeType, _) <- context typeName
  let (params, _) = bindingsView Abstract.piView $ first plicitness dataTypeType
      inst = instantiateTele (pure . snd <$> paramVars)
  paramVars <- forTele params $ \h p s -> do
    v <- exists h (inst s) ()
    return (p, v)

  let pureParamVars  = fmap pure <$> paramVars
      dataType = Abstract.apps (Abstract.Global typeName) pureParamVars
      implicitParamVars = (\(_p, v) -> (Implicit, pure v)) <$> paramVars

  (expr2, etype2) <- subtype surrounding expr1 etype1 dataType

  let go (c, nps, sbr) (etype, resBrs, resType) = do
        args <- V.forM nps $ \(h, p) -> do
          t <- existsVar h Abstract.Type ()
          v <- forall_ h t ()
          return (p, pure v)
        let qc = qualify typeName c
            pureVs = snd <$> args
        (paramsArgsExpr, etype') <- checkType
          surrounding
          (Concrete.apps (Concrete.Con $ Right qc) $ implicitParamVars <> args)
          etype
        (br, resType') <- checkType surrounding (instantiateTele pureVs sbr) resType

        let (_, args') = Abstract.appsView paramsArgsExpr
            vs = V.fromList $ map (\(p, arg) -> (p, case arg of
                Abstract.Var v -> Just v
                _ -> Nothing)) $ drop (teleLength params) args'
        sbr' <- abstractM (teleAbstraction (snd <$> vs) . Just) br
        let nps' = (\(p, mv) -> (maybe (Hint Nothing) metaHint mv, p)) <$> vs
        return (etype', (qc, nps', sbr'):resBrs, resType')

  resTypeT <- existsVar mempty Abstract.Type ()
  resType1 <- existsVar mempty resTypeT ()

  (etype3, cbrs2, resType2) <- foldrM go (etype2, mempty, resType1) cbrs

  (expr3, _etype3) <- subtype surrounding expr2 etype2 etype3

  modifyIndent pred
  tr "inferBranches res e" expr3
  tr "              res brs" $ ConBranches cbrs2
  tr "              res t" resType2
  return (expr3, ConBranches cbrs2, resType2)
inferBranches surrounding expr brs@(LitBranches lbrs d) = do
  tr "inferBranches e" expr
  tr "              brs" brs
  (expr', _etype') <- checkType surrounding expr Builtin.int
  t <- existsVar mempty Abstract.Type ()
  lbrs' <- forM lbrs $ \(l, e) -> do
    (e', _) <- checkType surrounding e t
    return (l, e')
  (d', t') <- checkType surrounding d t
  -- let brs' = LitBranches lbrs' d'
  tr "inferBranches res e" =<< freeze expr'
  -- tr "              res brs" brs'
  tr "              res t" =<< freeze t'
  return (expr', LitBranches lbrs' d', t')

generalise :: Abstract s -> Abstract s -> TCM s (Abstract s, Abstract s)
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
  :: Abstract s
  -> ConstrDef (Concrete s)
  -> TCM s (ConstrDef (Abstract s))
checkConstrDef typ (ConstrDef c (bindingsView Concrete.piView -> (args, ret))) = mdo
  let inst = instantiateTele $ (\(a, _, _, _) -> pure a) <$> args'
  args' <- forTele args $ \h p arg -> do
    argType <- existsVar h Abstract.Type ()
    (arg', _) <- checkType p (inst arg) argType
    v <- forall_ h arg' ()
    return (v, h, p, arg')

  (ret', _) <- checkType Explicit (inst ret) Abstract.Type
  unify ret' typ
  res <- F.foldrM (\(v, h, p, arg') rest ->
         Abstract.Pi h p arg' <$> abstract1M v rest) ret' args'
  return $ ConstrDef c res

checkDataType
  :: MetaVar s () Plicitness
  -> DataDef Concrete.Expr (MetaVar s () Plicitness)
  -> Abstract s
  -> TCM s ( DataDef (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
           , Abstract s
           )
checkDataType name (DataDef cs) typ = mdo
  typ' <- freeze typ
  tr "checkDataType t" typ'

  ps' <- forTele (Abstract.telescope typ') $ \h p s -> do
    let is = instantiateTele (pure <$> vs) s
    v <- forall_ h is ()
    return (v, h, p, is)

  let vs = (\(v, _, _, _) -> v) <$> ps'
      retType = Abstract.apps (pure name) [(p, pure v) | (v, _, p, _) <- V.toList ps']

  params <- forM ps' $ \(_, h, p, t) -> (,,) h p <$> abstractM (fmap Tele . (`V.elemIndex` vs)) t

  cs' <- forM cs $ \(ConstrDef c t) -> do
    res <- checkConstrDef retType (ConstrDef c $ instantiateTele (pure <$> vs) t)
    traverse (abstractM (fmap Tele . (`V.elemIndex` vs))) res

  let typ'' = quantify Abstract.Pi (Scope Abstract.Type) (Telescope params)

  tr "checkDataType res typ" typ''
  return (DataDef cs', typ'')

subDefType
  :: Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
  -> Abstract s
  -> Abstract s
  -> TCM s ( Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
           , Abstract s
           )
subDefType (Definition e) t t' = first Definition <$> subtype Explicit e t t'
subDefType (DataDefinition d) t t' = do unify t t'; return (DataDefinition d, t')

abstractDefM
  :: (MetaVar s () Plicitness -> Maybe b)
  -> Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
  -> Abstract s
  -> TCM s ( Definition (Abstract.Expr Plicitness) (Var b (MetaVar s () Plicitness))
           , ScopeM b (Abstract.Expr Plicitness) s () Plicitness
           )
abstractDefM f (Definition e) t = do
  e' <- abstractM f e
  t' <- abstractM f t
  return (Definition $ fromScope e', t')
abstractDefM f (DataDefinition e) t = do
  e' <- abstractDataDefM f e t
  t' <- abstractM f t
  return (DataDefinition e', t')

abstractDataDefM
  :: (MetaVar s () Plicitness -> Maybe b)
  -> DataDef (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
  -> Abstract s
  -> TCM s (DataDef (Abstract.Expr Plicitness) (Var b (MetaVar s () Plicitness)))
abstractDataDefM f (DataDef cs) typ = mdo
  let inst = instantiateTele $ pure <$> vs
      vs = (\(_, _, _, v) -> v) <$> ps'
  typ' <- freeze typ
  ps' <- forTele (Abstract.telescope typ') $ \h p s -> do
    let is = inst s
    v <- forall_ h is ()
    return (h, p, is, v)
  let f' x = F <$> f x <|> B . Tele <$> V.elemIndex x vs
  acs <- forM cs $ \c -> traverse (fmap (toScope . fmap assoc . fromScope) . abstractM f' . inst) c
  return $ DataDef acs
  where
    assoc :: Var (Var a b) c -> Var a (Var b c)
    assoc = unvar (unvar B (F . B)) (F . F)

checkDefType
  :: MetaVar s () Plicitness
  -> Definition Concrete.Expr (MetaVar s () Plicitness)
  -> Abstract s
  -> TCM s ( Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
           , Abstract s
           )
checkDefType _ (Definition e) typ = first Definition <$> checkType Explicit e typ
checkDefType v (DataDefinition d) typ = first DataDefinition <$> checkDataType v d typ

generaliseDef
  :: Vector (MetaVar s () Plicitness)
  -> Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
  -> Abstract s
  -> TCM s ( Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
           , Abstract s
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
  -- * Abstract vs on top of typ
  typ' <- foldrM (\v -> fmap (Abstract.Pi (metaHint v) Implicit (metaType v))
                      . abstract1M v) typ vs
  return (DataDefinition (DataDef cs'), typ')
  where
    f v = pure $ maybe (F v) (B . Tele) (v `V.elemIndex` vs)
    g = pure . B . (+ Tele (length vs))


generaliseDefs
  :: Vector ( MetaVar s () Plicitness
            , Definition (Abstract.Expr Plicitness) (MetaVar s () Plicitness)
            , Abstract s
            )
  -> TCM s (Vector ( Definition (Abstract.Expr Plicitness) (Var Int (MetaVar s () Plicitness))
                   , ScopeM Int (Abstract.Expr Plicitness) s () Plicitness
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
            , Definition Concrete.Expr (Var Int (MetaVar s () Plicitness))
            , ScopeM Int Concrete.Expr s () Plicitness
            )
  -> TCM s (Vector ( Definition (Abstract.Expr Plicitness) (Var Int (MetaVar s () Plicitness))
                   , ScopeM Int (Abstract.Expr Plicitness) s () Plicitness
                   )
           )
checkRecursiveDefs ds =
  generaliseDefs <=< enterLevel $ do
    evs <- V.forM ds $ \(v, _, _) -> do
      tv <- existsVar mempty Abstract.Type ()
      forall_ v tv ()
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( instantiateDef (pure . (evs V.!)) e
          , instantiate (pure . (evs V.!)) t
          )
    sequence $ flip V.imap instantiatedDs $ \i (d, t) -> do
      (t', _) <- checkType Explicit t Abstract.Type
      let v = evs V.! i
      unify (metaType v) t'
      (d', t'') <- checkDefType v d t'
      return (v, d', t'')
