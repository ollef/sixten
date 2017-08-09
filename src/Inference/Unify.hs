{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Unify where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.Monoid
import Data.List
import qualified Data.Set as Set
import Data.STRef
import qualified Data.Vector as Vector
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import qualified Builtin
import Inference.Normalise
import Inference.TypeOf
import Meta
import Syntax
import Syntax.Abstract
import VIX

existsType :: Monad e => NameHint -> VIX (e MetaA)
existsType n = existsVar n Builtin.Type

occurs
  :: [(AbstractM, AbstractM)]
  -> Level
  -> MetaA
  -> AbstractM
  -> VIX ()
occurs cxt l tv expr = traverse_ go expr
  where
    go tv'@(MetaVar _ typ _ mr)
      | tv == tv' = do
        loc <- currentLocation
        explanation <- forM cxt $ \(t1, t2) -> do
          t1' <- zonk t1
          t2' <- zonk t2
          actual <- showMeta t1'
          expect <- showMeta t2'
          return
            [ ""
            , Leijen.bold "Inferred: " <> Leijen.red actual
            , Leijen.bold "Expected: " <> Leijen.dullgreen expect
            ]
        printedTv <- showMeta (pure tv' :: AbstractM)
        expr' <- zonk expr
        printedExpr <- showMeta expr'
        throwError
          $ show (explain loc
            $ Err
              (Just "Cannot construct the infinite type")
              ([ Leijen.dullblue printedTv
               , "="
               , Leijen.dullblue printedExpr
               , ""
               , "while trying to unify"
               , ""
               ]
                ++
                intercalate ["", "while trying to unify"] explanation)
              mempty
              mempty)
      | otherwise = do
        occurs cxt l tv typ
        case mr of
          Nothing -> return ()
          Just r  -> do
            sol <- solution r
            case sol of
              Left l'    -> liftST $ writeSTRef r $ Left $ min l l'
              Right typ' -> traverse_ go typ'

unify :: [(AbstractM, AbstractM)] -> AbstractM -> AbstractM -> VIX ()
unify cxt type1 type2 = do
  logMeta 30 "unify t1" type1
  logMeta 30 "      t2" type2
  type1' <- zonk =<< whnf type1
  type2' <- zonk =<< whnf type2
  unify' ((type1', type2') : cxt) type1' type2'

unify' :: [(AbstractM, AbstractM)] -> AbstractM -> AbstractM -> VIX ()
unify' cxt type1 type2
  | type1 == type2 = return ()
  | otherwise = case (type1, type2) of
    -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
    -- distinct universally quantified variables, then 'f = \xs. t' is a most
    -- general solution (see Miller, Dale (1991) "A Logic programming...")
    (appsView -> (Var v@(metaRef -> Just r), distinctForalls -> Just pvs), _) -> solveVar unify r v pvs type2
    (_, appsView -> (Var v@(metaRef -> Just r), distinctForalls -> Just pvs)) -> solveVar (flip . unify) r v pvs type1
    (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) t1 t2 s1 s2
    (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) t1 t2 s1 s2
    -- Since we've already tried reducing the application, we can only hope to
    -- unify it pointwise.
    (App e1 a1 e1', App e2 a2 e2') | a1 == a2 -> do
      unify cxt e1  e2
      unify cxt e1' e2'
    _ -> do
      loc <- currentLocation
      explanation <- forM cxt $ \(t1, t2) -> do
        t1' <- zonk t1
        t2' <- zonk t2
        actual <- showMeta t1'
        expect <- showMeta t2'
        return
          [ ""
          , Leijen.bold "Inferred: " <> Leijen.red actual
          , Leijen.bold "Expected: " <> Leijen.dullgreen expect
          ]
      throwError
        $ show
        $ explain loc
        $ Err
          (Just "Type mismatch")
          (intercalate ["", "while trying to unify"] explanation)
          mempty
          mempty
  where
    absCase h a b s1 s2 = do
      unify cxt a b
      v <- pure <$> forall h a
      unify cxt (instantiate1 v s1) (instantiate1 v s2)
    distinctForalls pes = case traverse isForall pes of
      Just pes' | distinct pes' -> Just pes'
      _ -> Nothing
    isForall (p, Var v@(metaRef -> Nothing)) = Just (p, v)
    isForall _ = Nothing
    distinct pes = Set.size (Set.fromList es) == length es where es = map snd pes
    solveVar recurse r v pvs t = do
      let pvs' = Vector.fromList pvs
      sol <- solution r
      case sol of
        Left l -> do
          occurs cxt l v t
          tele <- metaTelescopeM pvs'
          let abstr = teleAbstraction $ snd <$> pvs'
          t' <- lams tele <$> abstractM abstr t
          t'Type <- fmap (pis tele) $ abstractM abstr =<< typeOfM t
          recurse cxt (metaType v) t'Type
          logMeta 30 ("solving " <> show (metaId v)) t'
          solve r t'
        Right c -> recurse cxt (apps c $ map (second pure) pvs) t
