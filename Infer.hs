{-# LANGUAGE ViewPatterns #-}
module Infer where

import Bound
import Control.Monad.Except
import Control.Monad.ST()
import Data.Bifunctor
import Data.Foldable as F
import Data.Hashable
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import Data.Vector(Vector)
import qualified Data.Vector as V

import Annotation
import Hint
import qualified Core
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
                                   (instantiate1 (return $ F v) s)
                                   (instantiate1 (return $ F v) ts)
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
    Input.Type      -> return (Core.Type, Core.Type)
    Input.Pi n p Nothing s -> do
      tv  <- existsVar mempty Core.Type ()
      v   <- forall_ n tv ()
      (e', _)  <- checkType surrounding (instantiate1 (return $ F v) s) Core.Type
      s'  <- abstract1M v e'
      return (Core.Pi n p tv s', Core.Type)
    Input.Pi n p (Just t) s -> do
      (t', _) <- checkType p t Core.Type
      v  <- forall_ n t' ()
      (e', _) <- checkType surrounding (instantiate1 (return $ F v) s) Core.Type
      s' <- abstract1M v e'
      return (Core.Pi n p t' s', Core.Type)
    Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
      a   <- existsVar mempty Core.Type ()
      b   <- existsVar mempty Core.Type ()
      x   <- forall_ n a ()
      (e', b')  <- checkType surrounding (instantiate1 (return $ F x) s) b
      s'  <- abstract1M x e'
      ab  <- abstract1M x b'
      return (Core.Lam n p a s', Core.Pi n p a ab)
    Input.App e1 p e2 -> do
      (e1', vt, s) <- inferPi surrounding e1 p
      (e2', _) <- checkType p e2 vt
      return (Core.App e1' p e2', instantiate1 e2' s)
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

-- TODO can this be replaced with subtyping?
inferPi :: (Hashable v, Ord v, Show v)
        => Plicitness -> Input s v -> Plicitness
        -> TCM s v (Core s v, Core s v, ScopeM () Core.Expr s () Plicitness v)
inferPi surrounding expr p = do
  tr "inferPi" expr
  modifyIndent succ
  (e, t) <- inferType surrounding expr
  (a, b, c) <- go True e t
  modifyIndent pred
  tr "inferPi res a" a
  tr "            b" b
  cv <- forallVar mempty Core.Type ()
  tr "            c" $ instantiate1 cv c
  return (a, b, c)
  where
    go reduce e t = case t of
      Core.Pi _ p' vt s | p == p' -> return (e, vt, s)
      Core.Pi h Implicit vt s     -> do
        v <- existsVar h vt ()
        go True (Core.betaApp e Implicit v) (instantiate1 v s)
      Core.Var (F v@(metaRef -> Just r)) -> do
        sol <- solution r
        unify (metaType v) Core.Type
        case sol of
          Left l -> do
            t1 <- existsVarAtLevel (metaHint v) Core.Type () l
            t2 <- existsVarAtLevel (metaHint v) Core.Type () l
            let at2 = abstractNone t2
            solve r $ Core.Pi mempty p t1 at2
            return (e, t1, at2)
          Right c -> go True e c
      _ | reduce                  -> go False e =<< whnf mempty plicitness t
      _                           -> do
        s <- showMeta t
        throwError $ "Expected function, got " ++ show s

generalise :: (Ord v, Show v) => Core s v -> Core s v -> TCM s v (Core s v, Core s v)
generalise expr typ = do
  tr "generalise e" expr
  tr "           t" typ
  modifyIndent succ

  fvs <- foldMapM (:[]) typ
  l   <- level
  let p (metaRef -> Just r) = either (> l) (const False) <$> solution r
      p _                   = return False
  fvs' <- filterM p fvs

  deps <- M.fromList <$> forM fvs' (\x -> do
    ds <- foldMapM S.singleton $ metaType x
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

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector
                     ( NameHint
                     , Scope Int Input.Expr (Var v (MetaVar s () Plicitness v))
                     , Scope Int Input.Expr (Var v (MetaVar s () Plicitness v))
                     )
                   -> TCM s v
                     ( Vector (ScopeM Int Core.Expr s () Plicitness v
                     , ScopeM Int Core.Expr s () Plicitness v)
                     )
checkRecursiveDefs ds = do
  (evs, checkedDs) <- enterLevel $ do
    evs <- V.forM ds $ \(v, _, _) -> do
      tv <- existsVar mempty Core.Type ()
      forall_ v tv ()
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( instantiate (return . return . (evs V.!)) e
          , instantiate (return . return . (evs V.!)) t
          )
    checkedDs <- V.forM instantiatedDs $ \(e, t) -> do
      (t', _) <- checkType Explicit t Core.Type
      (e', t'') <- checkType Explicit e t'
      return (e', t'')
    return (evs, checkedDs)
  V.forM checkedDs $ \(e, t) -> do
    (ge, gt) <- generalise e t
    tr "checkRecursiveDefs ge" ge
    tr "                   gt" gt
    s  <- abstractM (`V.elemIndex` evs) ge
    ts <- abstractM (`V.elemIndex` evs) gt
    return (s, ts)
