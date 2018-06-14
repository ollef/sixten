{-# LANGUAGE FlexibleContexts, OverloadedStrings, ViewPatterns #-}
module Inference.Unify where

import Control.Monad.Except
import Data.Bifoldable
import Data.Bifunctor
import Data.Foldable
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.HashSet(HashSet)
import Data.List
import Data.Monoid
import Data.STRef
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Data.Void

import Analysis.Simplify
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Inference.Normalise hiding (whnf)
import {-# SOURCE #-} Inference.Constraint
import Inference.TypeOf
import MonadContext
import Pretty
import Syntax
import Syntax.Abstract
import TypedFreeVar
import Util
import VIX

occurs
  :: [(AbstractM, AbstractM)]
  -> Level
  -> MetaVar
  -> AbstractM
  -> Infer ()
occurs cxt l mv expr = bitraverse_ go pure expr
  where
    go mv'
      | mv == mv' = do
        explanation <- forM cxt $ \(t1, t2) -> do
          t1' <- zonk t1
          t2' <- zonk t2
          actual <- prettyMeta t1'
          expect <- prettyMeta t2'
          return
            [ ""
            , bold "Inferred:" PP.<+> red actual
            , bold "Expected:" PP.<+> dullGreen expect
            ]
        printedTv <- prettyMetaVar mv'
        expr' <- zonk expr
        printedExpr <- prettyMeta expr'
        throwLocated
          $ "Cannot construct the infinite type"
          <> PP.line
          <> PP.vcat
            ([ dullBlue printedTv
            , "="
            , dullBlue printedExpr
            , ""
            , "while trying to unify"
            ] ++ intercalate ["", "while trying to unify"] explanation)
      | otherwise = do
        -- occurs cxt l mv $ vacuous $ metaType mv'
        sol <- solution mv'
        case sol of
          Left l' -> liftST $ writeSTRef (metaRef mv') $ Left $ min l l'
          Right expr' -> traverse_ go $ vacuous expr'

prune :: HashSet FreeV -> AbstractM -> Infer AbstractM
prune allowedVars expr = inUpdatedContext (const mempty) $ bindMetas go expr
  where
    go m es = indentLog $ do
      logShow 30 "prune" $ metaId m
      sol <- solution m
      case sol of
        Right e -> do
          VIX.logShow 30 "prune solved" ()
          bindMetas go $ betaApps (vacuous e) es
        Left l -> do
          locals <- toHashSet <$> localVars
          case distinctVars es of
            Nothing -> do
              VIX.logShow 30 "prune not distinct" ()
              return $ Meta m es
            Just pvs
              | Vector.length vs' == Vector.length vs -> do
                VIX.logShow 30 "prune nothing to do" ()
                return $ Meta m es
              | otherwise -> do
                let m'Type = pis (varTelescope' pvs') $ abstract (teleAbstraction vs') mType
                m'Type' <- bindMetas go m'Type
                let typeFvs = toHashSet m'Type'
                logMeta 30 "prune m'Type'" m'Type'
                logShow 30 "prune vs" $ varId <$> vs
                logShow 30 "prune vs'" $ varId <$> vs'
                logShow 30 "prune typeFvs" $ varId <$> toList typeFvs
                if HashSet.null typeFvs then do
                  m' <- existsAtLevel
                    (metaHint m)
                    (metaPlicitness m)
                    (assertClosed m'Type')
                    (Vector.length vs')
                    (metaSourceLoc m)
                    l
                  let e = Meta m' $ (\v -> (varData v, pure v)) <$> vs'
                      e' = lams (varTelescope' pvs) $ abstract (teleAbstraction vs) e
                  logShow 30 "prune varTypes" =<< (mapM (prettyMeta . varType) vs)
                  logShow 30 "prune vs'" $ varId <$> vs'
                  logShow 30 "prune varTypes'" =<< (mapM (prettyMeta . varType) vs')
                  logMeta 30 "prune e'" e'
                  solve m $ assertClosed e'
                  return e
                else
                  return $ Meta m es
              | otherwise -> return $ Meta m es
              where
                allowed = allowedVars <> locals
                assertClosed :: Functor f => f FreeV -> f Void
                assertClosed = fmap $ error "prune assertClosed"
                pvs' = Vector.filter ((`HashSet.member` allowed) . snd) pvs
                vs = snd <$> pvs
                vs' = snd <$> pvs'
                Just mType = typeApps (vacuous $ metaType m) es

unify :: [(AbstractM, AbstractM)] -> AbstractM -> AbstractM -> Infer ()
unify cxt type1 type2 = do
  logMeta 30 "unify t1" type1
  logMeta 30 "      t2" type2
  type1' <- zonk =<< whnf type1
  type2' <- zonk =<< whnf type2
  touchable <- getTouchable
  unify' ((type1', type2') : cxt) touchable type1' type2'

unify' :: [(AbstractM, AbstractM)] -> (MetaVar -> Bool) -> AbstractM -> AbstractM -> Infer ()
unify' cxt touchable type1 type2
  | type1 == type2 = return () -- TODO make specialised equality function to get rid of zonking in this and subtyping
  | otherwise = case (type1, type2) of
    (Pi h1 p1 t1 s1, Pi h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    (Lam h1 p1 t1 s1, Lam h2 p2 t2 s2) | p1 == p2 -> absCase (h1 <> h2) p1 t1 t2 s1 s2
    -- Eta-expand
    (Lam h p t s, _) -> do
      v <- forall h p t
      withVar v $ unify cxt (instantiate1 (pure v) s) (App type2 p $ pure v)
    (_, Lam h p t s) -> do
      v <- forall h p t
      withVar v $ unify cxt (App type1 p $ pure v) (instantiate1 (pure v) s)
    -- Eta-reduce
    (etaReduce -> Just type1', _) -> unify cxt type1' type2
    (_, etaReduce -> Just type2') -> unify cxt type1 type2'
    -- If we have 'unify (f xs) t', where 'f' is an existential, and 'xs' are
    -- distinct universally quantified variables, then 'f = \xs. t' is a most
    -- general solution (see Miller, Dale (1991) "A Logic programming...")
    (appsView -> (Meta m es1, es2), _) | touchable m, Just pvs <- distinctVars (es1 <> toVector es2) -> solveVar unify m pvs type2
    (_, appsView -> (Meta m es1, es2)) | touchable m, Just pvs <- distinctVars (es1 <> toVector es2) -> solveVar (flip . unify) m pvs type1
    -- Since we've already tried reducing the application, we can only hope to
    -- unify it pointwise.
    (App e1 p1 e1', App e2 p2 e2') | p1 == p2 -> do
      unify cxt e1  e2
      unify cxt e1' e2'
    _ -> do
      explanation <- forM cxt $ \(t1, t2) -> do
        t1' <- zonk t1
        t2' <- zonk t2
        actual <- prettyMeta t1'
        expect <- prettyMeta t2'
        return
          [ ""
          , bold "Inferred:" PP.<+> red actual
          , bold "Expected:" PP.<+> dullGreen expect
          ]
      throwLocated
        $ "Type mismatch" <> PP.line <>
          PP.vcat (intercalate ["", "while trying to unify"] explanation)
  where
    absCase h p t1 t2 s1 s2 = do
      unify cxt t1 t2
      v <- forall h p t1
      withVar v $ unify cxt (instantiate1 (pure v) s1) (instantiate1 (pure v) s2)
    solveVar recurse m pvs t = do
      sol <- solution m
      case sol of
        Left l -> do
          let vs = snd <$> pvs
          -- TODO pruning might need to take into account extra args like unify
          prunedt <- prune (toHashSet vs) t
          let lamt = lams (varTelescope' pvs) $ abstract (teleAbstraction vs) prunedt
          normLamt <- simplifyExpr (const False) 0 <$> zonk lamt
          logShow 30 "vs" (varId <$> vs)
          logMeta 30 ("solving t " <> show (metaId m)) t
          logMeta 30 ("solving prunedt " <> show (metaId m)) prunedt
          logMeta 30 ("solving lamt " <> show (metaId m)) lamt
          logMeta 30 ("solving normlamt " <> show (metaId m)) normLamt
          occurs cxt l m normLamt
          lamtType <- typeOf normLamt
          closedLamt <- traverse (\v -> error $ "Unify TODO error message" ++ shower (pretty v)) normLamt
          recurse cxt (vacuous $ metaType m) lamtType
          solve m closedLamt
        Right c -> recurse cxt (apps (vacuous c) $ second pure <$> pvs) t

distinctVars :: (Eq v, Hashable v, Traversable t) => t (p, Expr m v) -> Maybe (t (p, v))
distinctVars es = case traverse isVar es of
  Just es' | distinct (snd <$> es') -> Just es'
  _ -> Nothing

isVar :: (p, Expr m a) -> Maybe (p, a)
isVar (p, Var v) = Just (p, v)
isVar _ = Nothing

distinct :: (Foldable t, Hashable a, Eq a) => t a -> Bool
distinct es = HashSet.size (toHashSet es) == length es
