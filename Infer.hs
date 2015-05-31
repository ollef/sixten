{-# LANGUAGE ViewPatterns #-}
module Infer where

import Bound
import Bound.Var
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

checkType :: (Hashable v, Ord v, Show v) => Input s v -> Core s v -> TCM s v (Core s v, Core s v)
checkType expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Input.Lam m p s -> do
      typ' <- whnf typ
      case typ' of
        Core.Pi h p' a ts | p == p' -> do
          v <- freshForall (h <> m) a
          (body, ts') <- checkType (instantiate1 (return $ F v) s)
                                   (instantiate1 (return $ F v) ts)
          expr' <- Core.Lam (m <> h) p a <$> abstract1M v body
          typ'' <- Core.Pi  (h <> m) p a <$> abstract1M v ts'
          return (expr', typ'')
        Core.Pi h p' a ts | plicitness p' == Implicit -> do
          v <- freshForall h a
          (expr', ts') <- checkType expr (instantiate1 (return $ F v) ts)
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
        (expr', typ') <- inferType expr
        subtype expr' typ' typ

inferType :: (Hashable v, Ord v, Show v) => Input s v -> TCM s v (Core s v, Core s v)
inferType expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Input.Var (B v) -> do
      (_, typ, _) <- context v
      return (return $ B v, bimap plicitness B typ)
    Input.Var (F v) -> return (Core.Var $ F v, metaType v)
    Input.Type      -> return (Core.Type, Core.Type)
    Input.Pi n p Nothing s -> do
      tv  <- freshExistsV mempty Core.Type
      v   <- freshForall n tv
      (e', _)  <- checkType (instantiate1 (return $ F v) s) Core.Type
      s'  <- abstract1M v e'
      return (Core.Pi n p tv s', Core.Type)
    Input.Pi n p (Just t) s -> do
      (t', _) <- checkType t Core.Type
      v  <- freshForall n t'
      (e', _) <- checkType (instantiate1 (return $ F v) s) Core.Type
      s' <- abstract1M v e'
      return (Core.Pi n p t' s', Core.Type)
    Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
      a   <- freshExistsV mempty Core.Type
      b   <- freshExistsV mempty Core.Type
      x   <- freshForall n a
      (e', b')  <- checkType (instantiate1 (return $ F x) s) b
      s'  <- abstract1M x e'
      ab  <- abstract1M x b'
      return (Core.Lam n p a s', Core.Pi n p a ab)
    Input.App e1 p e2 -> do
      (e1', vt, s) <- inferPi e1 p
      (e2', _) <- checkType e2 vt
      return (Core.App e1' p e2', instantiate1 e2' s)
    Input.Anno e t  -> do
      (t', _) <- checkType t Core.Type
      checkType e t'
    Input.Wildcard  -> do
      t <- freshExistsV mempty Core.Type
      x <- freshExistsV mempty t
      return (x, t)
  modifyIndent pred
  tr "inferType res e" e
  tr "              t" t
  return (e, t)

inferPi :: (Hashable v, Ord v, Show v)
        => Input s v -> Plicitness
        -> TCM s v (Core s v, Core s v, CoreScope s () v)
inferPi expr p = do
  tr "inferPi" expr
  modifyIndent succ
  (e, t) <- inferType expr
  (a, b, c) <- go True e t
  modifyIndent pred
  tr "inferPi res a" a
  tr "            b" b
  cv <- freshForallV mempty Core.Type
  tr "            c" $ instantiate1 cv c
  return (a, b, c)
  where
    go reduce e t = case t of
      Core.Pi _ p' vt s | p == p' -> return (e, vt, s)
      Core.Pi h Implicit vt s     -> do
        v <- freshExistsV h vt
        go True (Core.betaApp e Implicit v) (instantiate1 v s)
      Core.Var (F v@(metaRef -> Just r)) -> do
        sol <- solution r
        unify (metaType v) Core.Type
        case sol of
          Left l -> do
            t1 <- freshExistsLV (metaHint v) Core.Type l
            t2 <- freshExistsLV (metaHint v) Core.Type l
            let at2 = abstractNone t2
            solve r $ Core.Pi mempty p t1 at2
            return (e, t1, at2)
          Right c -> go True e c
      _ | reduce                  -> go False e =<< whnf t
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

checkAndGeneralise :: (Hashable v, Ord v, Show v)
                   => Input s v -> Core s v
                   -> TCM s v (Core.Expr Plicitness v, Core.Type Plicitness v)
checkAndGeneralise e t = do
  (tce, tct) <- enterLevel $ checkType e t
  (ge, gt)   <- generalise tce tct
  ge'        <- traverse (unvar return $ const $ throwError "escaped type variable") ge
  gt'        <- traverse (unvar return $ const $ throwError "escaped type variable") gt
  return (ge', gt')

checkRecursiveDefs :: (Hashable v, Ord v, Show v)
                   => Vector (NameHint, InputScope s Int v, InputScope s Int v)
                   -> TCM s v (Vector (CoreScope s Int v, CoreScope s Int v))
checkRecursiveDefs ds = do
  (evs, checkedDs) <- enterLevel $ do
    evs <- V.forM ds $ \(v, _, _) -> do
      tv <- freshExistsV mempty Core.Type
      freshForall v tv
    let instantiatedDs = flip V.map ds $ \(_, e, t) ->
          ( instantiate (return . return . (evs V.!)) e
          , instantiate (return . return . (evs V.!)) t
          )
    checkedDs <- V.forM instantiatedDs $ \(e, t) -> do
      (t', _) <- checkType t Core.Type
      (e', t'') <- checkType e t'
      return (e', t'')
    return (evs, checkedDs)
  V.forM checkedDs $ \(e, t) -> do
    (ge, gt) <- generalise e t
    tr "checkRecursiveDefs ge" ge
    tr "                   gt" gt
    s  <- abstractM (`V.elemIndex` evs) ge
    ts <- abstractM (`V.elemIndex` evs) gt
    return (s, ts)
