{-# LANGUAGE FlexibleContexts, ViewPatterns #-}
module Unify where

import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Foldable
import Data.Monoid
import qualified Data.Set as Set
import qualified Data.Vector as Vector
import Data.STRef

import qualified Builtin
import Meta
import Normalise
import Syntax
import Syntax.Abstract
import TCM
import TypeOf

existsSize :: Monad e => NameHint -> TCM (e (MetaVar ExprP))
existsSize n = existsVar n Builtin.Size

existsType :: Monad e => NameHint -> TCM (e (MetaVar ExprP))
existsType n = do
  sz <- existsSize n
  existsVar n $ Builtin.TypeP sz

existsTypeType :: NameHint -> TCM (ExprP (MetaVar ExprP))
existsTypeType h = do
  sz <- existsSize h
  return $ Builtin.TypeP sz

occurs
  :: Foldable e
  => Level
  -> MetaVar e
  -> e (MetaVar e)
  -> TCM ()
occurs l tv = traverse_ go
  where
    go tv'@(MetaVar _ typ _ mr)
      | tv == tv' = throwError "occurs check"
      | otherwise = do
        occurs l tv typ
        case mr of
          Nothing -> return ()
          Just r  -> do
            sol <- solution r
            case sol of
              Left l'    -> liftST $ writeSTRef r $ Left $ min l l'
              Right typ' -> occurs l tv typ'

unify :: AbstractM -> AbstractM -> TCM ()
unify type1 type2 = do
  logMeta 30 "unify t1" type1
  logMeta 30 "      t2" type2
  type1' <- whnf type1
  type2' <- whnf type2
  unify' type1' type2'

unify' :: AbstractM -> AbstractM -> TCM ()
unify' type1 type2
  | type1 == type2 = return ()
  | otherwise = case (type1, type2) of
    -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
    -- distinct universally quantified variables, then 'f = \xs. t' is a most
    -- general solution (see Miller, Dale (1991) "A Logic programming...")
    (appsView -> (Var v@(metaRef -> Just r), distinctForalls -> Just pvs), _) -> solveVar r v pvs type2
    (_, appsView -> (Var v@(metaRef -> Just r), distinctForalls -> Just pvs)) -> solveVar r v pvs type1
    (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    (Lit 0, Builtin.AddSizeE x y) -> do
      unify (Lit 0) x
      unify (Lit 0) y
    (Builtin.AddSizeE x y, Lit 0) -> do
      unify x (Lit 0)
      unify y (Lit 0)
    (Builtin.AddSizeE (Lit m) y, Lit n) -> unify y $ Lit $ n - m
    (Builtin.AddSizeE y (Lit m), Lit n) -> unify y $ Lit $ n - m
    (Lit n, Builtin.AddSizeE (Lit m) y) -> unify y $ Lit $ n - m
    (Lit n, Builtin.AddSizeE y (Lit m)) -> unify y $ Lit $ n - m
    -- Since we've already tried reducing the application, we can only hope to
    -- unify it pointwise.
    (App e1 a1 e1', App e2 a2 e2') | a1 == a2 -> do
      unify e1  e2
      unify e1' e2'
    _ -> throwError
      $ "Can't unify types: "
      ++ show (pretty (show <$> type1, show <$> type2))
  where
    absCase h p a b s1 s2 = do
      unify a b
      v <- pure <$> forall h p a
      unify (instantiate1 v s1) (instantiate1 v s2)
    distinctForalls pes | distinct pes = traverse isForall pes
                        | otherwise = Nothing
    isForall (p, Var v@(metaRef -> Nothing)) = Just (p, v)
    isForall _ = Nothing
    distinct pes = Set.size (Set.fromList es) == length es where es = map snd pes
    solveVar r v pvs t = do
      let pvs' = Vector.fromList pvs
      sol <- solution r
      case sol of
        Left l -> do
          occurs l v t
          tele <- metaTelescopeM pvs'
          let abstr = teleAbstraction $ snd <$> pvs'
          t' <- lams tele <$> abstractM abstr t
          t'Type <- fmap (pis tele) $ abstractM abstr =<< typeOfM t
          unify (metaType v) t'Type
          logMeta 30 ("solving " <> show (metaId v)) t'
          solve r t'
        Right c -> unify (apps c $ map (second pure) pvs) t
