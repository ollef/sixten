{-# LANGUAGE BangPatterns, ViewPatterns, RecursiveDo #-}
module Infer where

import Bound
import Bound.Var
import Control.Applicative
import Control.Monad.Except
import Control.Monad.ST()
import Data.Bifunctor
import Data.Foldable as F
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.Monoid
import qualified Data.HashSet as HS
import Data.Vector(Vector)
import qualified Data.Vector as V

import Annotation
import Data
import qualified Core
import Hint
import qualified Input
import Meta
import Monad
import Normalise
import TopoSort
import Unify
import Util

type Input s v = InputM s () Plicitness v

checkType :: (Hashable v, Ord v, Show v)
          => Plicitness -> Input s v -> Core s v -> TCM s v (Core s v, Core s v)
checkType surrounding expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Input.Lam m p s -> do
      typ' <- whnf mempty plicitness typ
      case typ' of
        Core.Pi h p' a ts | p == p' -> do
          v <- forall_ (h <> m) a ()
          (body, ts') <- checkType surrounding
                                   (instantiate1 (pure $ F v) s)
                                   (instantiate1 (pure $ F v) ts)
          expr' <- Core.Lam (m <> h) p a <$> abstract1M v body
          typ'' <- Core.Pi  (h <> m) p a <$> abstract1M v ts'
          return (expr', typ'')
        Core.Pi h p' a ts | p' == Implicit -> do
          v <- forall_ h a ()
          (expr', ts') <- checkType surrounding expr (instantiate1 (return $ F v) ts)
          typ''  <- Core.Pi  h p' a <$> abstract1M v ts'
          expr'' <- Core.Lam h p' a <$> abstract1M v expr'
          return (expr'', typ'')
        _ -> inferIt
    _ -> inferIt
  modifyIndent pred
  tr "checkType res e" rese
  tr "              t" rest
  return (rese, rest)
    where
      inferIt = do
        (expr', typ') <- inferType surrounding expr
        subtype surrounding expr' typ' typ

inferType :: (Hashable v, Ord v, Show v)
          => Plicitness -> Input s v -> TCM s v (Core s v, Core s v)
inferType surrounding expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Input.Var (B v) -> do
      (_, typ, _) <- context v
      return (return $ B v, bimap plicitness B typ)
    Input.Var (F v) -> return (Core.Var $ F v, metaType v)
    Input.Con c -> do
      typ <- constructor c
      return (Core.Con c, bimap plicitness B typ)
    Input.Type -> return (Core.Type, Core.Type)
    Input.Pi n p t s -> do
      (t', _) <- checkType p t Core.Type
      v  <- forall_ n t' ()
      (e', _) <- checkType surrounding (instantiate1 (return $ F v) s) Core.Type
      s' <- abstract1M v e'
      return (Core.Pi n p t' s', Core.Type)
    Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
      a <- existsVar mempty Core.Type ()
      b <- existsVar mempty Core.Type ()
      x <- forall_ n a ()
      (e', b')  <- checkType surrounding (instantiate1 (return $ F x) s) b
      s' <- abstract1M x e'
      ab <- abstract1M x b'
      return (Core.Lam n p a s', Core.Pi n p a ab)
    Input.App e1 p e2 -> do
      a <- existsVar mempty Core.Type ()
      b <- existsVar mempty Core.Type ()
      (e1', e1type) <- checkType surrounding e1 $ Core.Pi mempty p a
                                                $ abstractNone b
      case e1type of
        Core.Pi _ p' a' b' | p == p' -> do
          (e2', _) <- checkType p e2 a'
          return (Core.App e1' p e2', instantiate1 e2' b')
        _ -> throwError "inferType: expected pi type"
    Input.Case e brs -> do
      undefined
    Input.Anno e t  -> do
      (t', _) <- checkType surrounding t Core.Type
      checkType surrounding e t'
    Input.Wildcard  -> do
      t <- existsVar mempty Core.Type ()
      x <- existsVar mempty t ()
      return (x, t)
  modifyIndent pred
  tr "inferType res e" e
  tr "              t" t
  return (e, t)

generalise :: (Show v, Ord v)
           => Core s v -> Core s v -> TCM s v (Core s v, Core s v)
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
  genexpr <- F.foldrM ($ Core.etaLam) expr sorted
  gentype <- F.foldrM ($ Core.Pi)     typ  sorted

  modifyIndent pred
  tr "generalise res ge" genexpr
  tr "               gt" gentype
  return (genexpr, gentype)
  where
    go [a] f = fmap (f (metaHint a) Implicit $ metaType a) . abstract1M a
    go _   _ = error "Generalise"

checkConstrDef :: (Ord v, Show v, Hashable v)
               => Core s v
               -> ConstrDef (Input s v)
               -> TCM s v (ConstrDef (Core s v))
checkConstrDef typ (ConstrDef c (bindingsView Input.piView -> (args, ret))) = mdo
  let inst = instantiate (\n -> let (a, _, _, _) = args' V.! n in pure $ F a)
  args' <- forM (V.fromList args) $ \(h, p, arg) -> do
    (arg', _) <- checkType p (inst arg) Core.Type
    v <- forall_ h arg' ()
    return (v, h, p, arg')
  (ret', _) <- checkType Explicit (inst ret) Core.Type
  unify ret' typ
  res <- F.foldrM (\(v, h, p, arg') rest ->
         Core.Pi h p arg' <$> abstract1M v rest) ret' args'
  return $ ConstrDef c res

extractParams :: Core.Expr p v -> Vector (NameHint, p, Scope Int (Core.Expr p) v)
extractParams (bindingsView Core.piView -> (ps, fromScope -> Core.Type))
  = V.fromList ps
extractParams _ = error "extractParams"

checkDataType :: (Hashable v, Ord v, Show v)
              => Var v (MetaVar s () Plicitness v)
              -> DataDef Input.Expr (Var v (MetaVar s () Plicitness v))
              -> Core s v
              -> TCM s v ( Data.DataDef (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
                         , Core s v
                         )
checkDataType name (DataDef _ps cs) typ = mdo
  let inst = instantiate (\n -> let (v, _, _, _) = ps' V.! n in pure $ F v)
  let inst' = instantiate (\n -> let (v, _, _, _) = ps' V.! n in pure $ F v)

  ps' <- forM (extractParams typ) $ \(h, p, s) -> do
    let is = inst s
    v <- forall_ h is ()
    return (v, h, p, is)

  let vs = (\(v, _, _, _) -> v) <$> ps'
      retType = Core.apps (pure name) [(p, pure $ F v) | (v, _, p, _) <- V.toList ps']

  params <- forM ps' $ \(_, h, p, t) -> (,,) h p <$> abstractM (`V.elemIndex` vs) t

  cs' <- forM cs $ \(ConstrDef c t) -> do
    res <- checkConstrDef retType (ConstrDef c $ inst' t)
    traverse (abstractM (`V.elemIndex` vs)) res

  return (DataDef params cs', typ)

subDefType :: (Ord v, Show v, Hashable v)
           => Input.Definition (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
           -> Core s v
           -> Core s v
           -> TCM s v ( Input.Definition (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
                      , Core s v
                      )
subDefType (Input.Definition e) t t' = first Input.Definition <$> subtype Explicit e t t'
subDefType (Input.DataDefinition d) t t' = do unify t t'; return (Input.DataDefinition d, t')

generaliseDef :: (Ord v, Show v)
              => Input.Definition (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
              -> Core s v
              -> TCM s v ( Input.Definition (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
                         , Core s v
                         )
generaliseDef (Input.Definition d) t = first Input.Definition <$> generalise d t
generaliseDef (Input.DataDefinition d) t = return (Input.DataDefinition d, t)

abstractDefM :: (Show a, Show v)
             => (MetaVar s () a v -> Maybe b)
             -> Input.Definition (Core.Expr a) (Var v (MetaVar s () a v))
             -> TCM s v (Input.Definition (Core.Expr a) (Var b (Var v (MetaVar s () a v))))
abstractDefM f (Input.Definition e) = Input.Definition . fromScope <$> abstractM f e
abstractDefM f (Input.DataDefinition e) = Input.DataDefinition <$> abstractDataDefM f e

abstractDataDefM :: (Show a, Show v)
                 => (MetaVar s () a v -> Maybe b)
                 -> DataDef (Core.Expr a) (Var v (MetaVar s () a v))
                 -> TCM s v' (DataDef (Core.Expr a) (Var b (Var v (MetaVar s () a v))))
abstractDataDefM f (DataDef ps cs) = mdo
  let inst = instantiate (pure . F . (vs V.!))
      vs = (\(_, _, _, v) -> v) <$> ps'
  ps' <- forM ps $ \(h, p, s) -> let is = inst s in (,,,) h p is <$> forall_ h is ()
  let f' x = F <$> f x <|> B <$> V.elemIndex x vs
  aps <- forM ps' $ \(h, p, s, _) -> (,,) h p <$> (toScope . fmap assoc . fromScope) <$> abstractM f' s
  acs <- forM cs $ \c -> traverse (fmap (toScope . fmap assoc . fromScope) . abstractM f' . inst) c
  return $ DataDef aps acs
  where
    assoc :: Var (Var a b) c -> Var a (Var b c)
    assoc = unvar (unvar B (F . B)) (F . F)

checkDefType :: (Hashable v, Ord v, Show v)
             => Var v (MetaVar s () Plicitness v)
             -> Input.Definition Input.Expr (Var v (MetaVar s () Plicitness v))
             -> Core s v
             -> TCM s v ( Input.Definition (Core.Expr Plicitness) (Var v (MetaVar s () Plicitness v))
                        , Core s v
                        )
checkDefType _ (Input.Definition e) typ = first Input.Definition <$> checkType Explicit e typ
checkDefType v (Input.DataDefinition d) typ = first Input.DataDefinition <$> checkDataType v d typ

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector
                     ( NameHint
                     , Input.Definition Input.Expr (Var Int (Var v (MetaVar s () Plicitness v)))
                     , Scope Int Input.Expr (Var v (MetaVar s () Plicitness v))
                     )
                   -> TCM s v
                     (Vector ( Input.Definition (Core.Expr Plicitness) (Var Int (Var v (MetaVar s () Plicitness v)))
                             , ScopeM Int Core.Expr s () Plicitness v
                             )
                     )
checkRecursiveDefs ds = do
  (evs, checkedDs) <- enterLevel $ do
    evs <- V.forM ds $ \(v, _, _) -> do
      tv <- existsVar mempty Core.Type ()
      forall_ v tv ()
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( Input.instantiateDef (pure . pure . (evs V.!)) e
          , instantiate (pure . pure . (evs V.!)) t
          )
    checkedDs <- sequence $ flip V.imap instantiatedDs $ \i (d, t) -> do
      (t', _) <- checkType Explicit t Core.Type
      (d', t'') <- checkDefType (F $ evs V.! i) d t'
      subDefType d' t'' (metaType $ evs V.! i)
    return (evs, checkedDs)
  V.forM checkedDs $ \(d, t) -> do
    (gd, gt) <- generaliseDef d t
    -- tr "checkRecursiveDefs gd" gd
    tr "                   gt" gt
    s  <- abstractDefM (`V.elemIndex` evs) gd
    ts <- abstractM (`V.elemIndex` evs) gt
    return (s, ts)
