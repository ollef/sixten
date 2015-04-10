{-# LANGUAGE ViewPatterns #-}
module Unify where

import Bound
import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Foldable
import qualified Data.Set as S
import Data.STRef

import Core
import Meta
import Monad
import Normalise
import Util

occurs :: Level -> MetaVar s -> Core s -> TCM s ()
occurs l tv = traverse_ go
  where
    go tv'@(MetaVar _ typ _ mr)
      | tv == tv'                    = throwError "occurs check"
      | otherwise = do
        occurs l tv typ
        case mr of
          Nothing -> return ()
          Just r  -> do
            sol <- solution r
            case sol of
              Left l'    -> liftST $ writeSTRef r $ Left $ min l l'
              Right typ' -> occurs l tv typ'

unify :: Core s -> Core s -> TCM s ()
unify type1 type2 = do
  tr "unify t1" type1
  tr "      t2" type2
  go True type1 type2
  where
    go reduce t1 t2
      | t1 == t2  = return ()
      | otherwise = case (t1, t2) of
        (Core.Var v1@(metaRef -> Just r1), Core.Var v2@(metaRef -> Just r2)) -> do
          unify (metaType v1) (metaType v2)
          sol1 <- solution r1
          sol2 <- solution r2
          case (sol1, sol2) of
            (Left l1, Left l2)
              | l1 <= l2  -> solve r2 t1
              | otherwise -> solve r1 t2
            (Right c1, _) -> go reduce c1 t2
            (_, Right c2) -> go reduce t1 c2
        -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs'
        -- are distinct universally quantified variables, then 'f = \xs. t' is
        -- a most general solution (See Miller, Dale (1991) "A Logic
        -- programming...")
        (Core.appsView -> (Core.Var v@(metaRef -> Just r), distinctForalls -> Just pvs), _) -> solveVar r v pvs t2
        (_, Core.appsView -> (Core.Var v@(metaRef -> Just r), distinctForalls -> Just pvs)) -> solveVar r v pvs t1
        (Core.Pi  h p1 a s1, Core.Pi  _ p2 b s2) | p1 == p2 -> absCase h a b s1 s2
        (Core.Lam h p1 a s1, Core.Lam _ p2 b s2) | p1 == p2 -> absCase h a b s1 s2

        -- If we've already tried reducing the application,
        -- we can only hope to unify it pointwise.
        (Core.App e1 p1 e1', Core.App e2 p2 e2') | p1 == p2 && not reduce -> do
          go True e1  e2
          go True e1' e2'
        (Core.Type, Core.Type) -> return ()
        _ | reduce             -> do
          t1' <- whnf t1
          t2' <- whnf t2
          go False t1' t2'
        _                      -> throwError "Can't unify types"
    absCase h a b s1 s2 = do
      go True a b
      v <- freshForall h a
      go True (instantiate1 (return v) s1) (instantiate1 (return v) s2)
    distinctForalls pes | distinct pes = traverse isForall pes
                        | otherwise    = Nothing
    isForall (p, Core.Var v@(metaRef -> Nothing)) = Just (p, v)
    isForall _                                    = Nothing
    distinct pes = S.size (S.fromList es) == length es where es = map snd pes
    solveVar r v pvs t = do
      sol <- solution r
      case sol of
        Left l  -> do
          occurs l v t
          solve r =<< lams pvs t
        Right c -> go True (Core.apps c (map (second return) pvs)) t
    lams pvs t = foldrM (\(p, v) -> fmap (Core.Lam (Hint Nothing) p $ metaType v) . abstract1M v) t pvs
