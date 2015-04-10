{-# LANGUAGE ViewPatterns #-}
module Infer where

import Bound
import Control.Monad.Except
import Control.Monad.ST()
import Data.Bitraversable
import Data.Foldable as F
import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import Text.Trifecta.Result

import qualified Core
import qualified Input
import Meta
import Monad
import Normalise
import qualified Parser
import Pretty
import TopoSort
import Unify
import Util

inferPi :: Input s -> Plicitness
        -> TCM s (Core s, Core s, Scope1 Core.Expr (MetaVar s))
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
      Core.Var v@(metaRef -> Just r) -> do
        sol <- solution r
        unify (metaType v) Core.Type
        case sol of
          Left l -> do
            t1 <- freshExistsLV (metaHint v) Core.Type l
            t2 <- freshExistsLV (metaHint v) Core.Type l
            let at2 = abstractNothing t2
            solve r $ Core.Pi mempty p t1 at2
            return (e, t1, at2)
          Right c -> go True e c
      _ | reduce                  -> go False e =<< whnf t
      _                           -> do
        s <- showMeta t
        throwError $ "Expected function, got " ++ show s

generalise :: Core s -> Core s -> TCM s (Core s, Core s)
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
  -- fexpr <- freeze expr
  -- ftyp  <- freeze typ
  genexpr <- F.foldrM ($ Core.etaLam) expr sorted
  gentype <- F.foldrM ($ Core.Pi)     typ  sorted

  modifyIndent pred
  tr "generalise res ge" genexpr
  tr "               gt" gentype
  return (genexpr, gentype)
  where
    go [a] f = fmap (f (metaHint a) Implicit $ metaType a) . abstract1M a
    go _   _ = error "Generalise"

inferType :: Input s -> TCM s (Core s, Core s)
inferType expr = do
  tr "inferType" expr
  modifyIndent succ
  (e, t) <- case expr of
    Input.Var v     -> return (Core.Var v, metaType v)
    Input.Type      -> return (Core.Type, Core.Type)
    Input.Pi n p Nothing s -> do
      tv  <- freshExistsV mempty Core.Type
      v   <- freshForall n tv
      (e', _)  <- checkType (instantiate1 (return v) s) Core.Type
      s'  <- abstract1M v e'
      return (Core.Pi n p tv s', Core.Type)
    Input.Pi n p (Just t) s -> do
      (t', _) <- checkType t Core.Type
      v  <- freshForall n t'
      (e', _) <- checkType (instantiate1 (return v) s) Core.Type
      s' <- abstract1M v e'
      return (Core.Pi n p t' s', Core.Type)
    Input.Lam n p s -> uncurry generalise <=< enterLevel $ do
      a   <- freshExistsV mempty Core.Type
      b   <- freshExistsV mempty Core.Type
      x   <- freshForall n a
      (e', b')  <- checkType (instantiate1 (return x) s) b
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

subtype :: Core s -> Core s -> Core s -> TCM s (Core s, Core s)
subtype expr type1 type2 = do
  tr "subtype e"  expr
  tr "        t1" type1
  tr "        t2" type2
  modifyIndent succ
  (e', type') <- go True expr type1 type2
  modifyIndent pred
  tr "subtype res e'" e'
  tr "            type'" type'
  return (e', type')
  where
    go reduce e typ1 typ2
      | typ1 == typ2 = return (e, typ2)
      | otherwise = case (typ1, typ2) of
        (Core.Pi h1 p1 t1 s1, Core.Pi h2 p2 t2 s2) | p1 == p2 -> do
          let h = h1 <> h2
          x2  <- freshForall h t2
          (x1, _)   <- subtype (return x2) t2 t1
          (ex, s2') <- subtype (Core.App e p1 x1)
                                (instantiate1 x1 s1)
                                (instantiate1 x1 s2)
          e2    <- Core.etaLam h p1 t2 <$> abstract1M x2 ex
          typ2' <- Core.Pi h p1 t2 <$> abstract1M x2 s2'
          return (e2, typ2')
        {-
        (Core.Pi n p t1 s1, Core.Var v@(metaRef -> Just r)) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ1
              unify (metaType v) Core.Type
              t2  <- freshExistsLV Core.Type l
              t2' <- freshExistsLV Core.Type l
              x2  <- freshExists t2
              solve r . Core.Pi n p t2 =<< abstract1M x2 t2'
              x1  <- subtype (return x2) t2 t1
              ex  <- subtype (Core.App e p x1) (instantiate1 x1 s1) t2'
              refineSolved r . Core.Pi n p t2 =<< abstract1M x2 t2'
              Core.etaLam n p t2 <$> abstract1M x2 ex
            Right c -> subtype e typ1 c
        -}
        (Core.Var v@(metaRef -> Just r), Core.Pi h p t2 s2) -> do
          sol <- solution r
          case sol of
            Left l -> do
              occurs l v typ2
              unify (metaType v) Core.Type
              t11  <- freshExistsLV (metaHint v) Core.Type l
              t12 <- freshExistsLV (metaHint v) Core.Type l
              solve r $ Core.Pi h p t11 $ abstractNothing t12
              x2  <- freshForall h t2
              (x1, t11') <- subtype (return x2) t2 t11
              (ex, s2')  <- subtype (Core.betaApp e p x1) t12 (instantiate1 (return x2) s2)
              refineSolved r . Core.Pi h p t11' =<< abstract1M x2 s2'
              e2    <- Core.etaLam h p t2 <$> abstract1M x2 ex
              typ2' <- Core.Pi h p t2 <$> abstract1M x2 s2'
              return (e2, typ2')
            Right c -> subtype e c typ2
        (_, Core.Pi h Implicit t2 s2) -> do
          x2 <- freshForall h t2
          (e2, s2') <- subtype e typ1 (instantiate1 (return x2) s2)
          e2'   <- Core.etaLam h Implicit t2 <$> abstract1M x2 e2
          typ2' <- Core.Pi     h Implicit t2 <$> abstract1M x2 s2'
          return (e2', typ2')
        (Core.Pi h Implicit t1 s1, _) -> do
          v1 <- freshExistsV h t1
          subtype (Core.betaApp e Implicit v1) (instantiate1 v1 s1) typ2
        _ | reduce -> do
          typ1' <- whnf typ1
          typ2' <- whnf typ2
          go False e typ1' typ2'
        _ -> do unify typ1 typ2; return (e, typ2)

checkType :: Input s -> Core s -> TCM s (Core s, Core s)
checkType expr typ = do
  tr "checkType e" expr
  tr "          t" =<< freeze typ
  modifyIndent succ
  (rese, rest) <- case expr of
    Input.Lam m p s -> do
      typ' <- whnf typ
      case typ' of
        Core.Pi h p' a ts | p == p' -> do
          v <- freshForall h a
          (body, ts') <- checkType (instantiate1 (return v) s)
                                   (instantiate1 (return v) ts)
          expr' <- Core.Lam m p a <$> abstract1M v body
          typ'' <- Core.Pi m p a <$> abstract1M v ts'
          return (expr', typ'')
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

data Empty
fromEmpty :: Empty -> a
fromEmpty = error "fromEmpty"

infer :: Input.Expr Empty -> (Either String (Doc, Doc), [String])
infer e = runTCM
        $ bimapM showMeta showMeta <=< bimapM freeze freeze <=< uncurry generalise <=< (enterLevel . inferType)
        $ fmap fromEmpty e

test :: String -> IO ()
test inp = case (infer . fmap (const undefined)) <$> Parser.test Parser.expr inp of
  Success (res, l) -> do
    putDoc $ pretty l
    putStrLn ""
    putStrLn ""
    putDoc $ pretty res
    putStrLn ""
  Failure d        -> putDoc d
