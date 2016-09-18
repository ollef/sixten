{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Erase where

import qualified Bound.Scope.Simple as Simple
import Bound.Scope
import Control.Monad.Except
import Data.Monoid
import qualified Data.Vector as Vector

import qualified Builtin
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.SLambda as SLambda
import Meta
import TCM
import Unify

eraseS :: AbstractM -> TCM SLambdaM
eraseS e = SLambda.Sized <$> (erase =<< sizeOf e) <*> erase e

erase :: AbstractM -> TCM LambdaM
erase expr = do
  tr "erase expr" expr
  modifyIndent succ
  res <- case expr of
    Abstract.Var v -> return $ SLambda.Var v
    Abstract.Global g -> return $ SLambda.Global g
    Abstract.Lit l -> return $ SLambda.Lit l
    Abstract.Pi {} -> return $ SLambda.Con Builtin.Unit mempty
    Abstract.Lam h a t s
      | relevance a == Relevant -> do
        v <- forall h t
        e <- eraseS $ instantiate1 (pure v) s
        sz <- erase =<< sizeOfType t
        return $ SLambda.Lam h sz $ Simple.abstract1 v e
      | otherwise -> do
        v <- forall h t
        erase $ instantiate1 (pure v) s
    (appsView -> (Abstract.Con qc, es)) -> do
      n <- constrArity qc
      case compare argsLen n of
        GT -> throwError $ "erase: too many args for constructor: " ++ show qc
        EQ -> SLambda.Con qc <$> mapM eraseS es'
        LT -> do
          conType <- qconstructor qc
          let Just appliedConType = typeApps conType $ snd <$> es
              tele = telescope appliedConType
          erase $ lams tele
                $ Scope
                $ apps (Abstract.Con qc)
                $ Vector.fromList (fmap (pure . pure) <$> es)
                <> forTele tele (\_ a t -> (a, unscope t))
      where
        es' = Vector.fromList $ snd <$> filter (\(a, _) -> relevance a == Relevant) es
        argsLen = length es
    Abstract.Con _qc -> throwError "erase impossible"
    Abstract.App e1 a e2
      | relevance a == Relevant -> SLambda.App <$> erase e1 <*> eraseS e2
      | otherwise -> erase e1
    Abstract.Case e brs -> SLambda.Case <$> eraseS e <*> eraseBranches brs
  modifyIndent pred
  tr "erase res" res
  return res

relevantAbstraction :: Telescope Scope Annotation expr v -> Tele -> Maybe Tele
relevantAbstraction tele (Tele n) = Tele <$> perm Vector.! n
  where
    perm = Vector.fromList $ reverse $ fst $
      Vector.foldl' (\(xs, i) (_, a, _) -> case relevance a of
          Irrelevant -> (Nothing : xs, i)
          Relevant -> (Just i : xs, i + 1))
        ([], 0) $ unTelescope tele

eraseBranches
  :: Pretty c
  => BranchesM c Abstract.Expr
  -> TCM (SimpleBranchesM c SLambda.Expr)
eraseBranches (ConBranches cbrs typ) = do
  tr "eraseBranches brs" $ ConBranches cbrs typ
  modifyIndent succ
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h a s -> do
      let t = instantiateTele pureVs s
      tsz <- erase =<< sizeOfType t
      v <- forall h t
      return (v, (h, a, Simple.abstract abstr tsz))
    let vs = fst <$> tele'
        abstr v = relevantAbstraction tele =<< teleAbstraction vs v
        pureVs = pure <$> vs
        tele'' = Telescope
               $ fmap (\(h, _, t) -> (h, (), t))
               $ Vector.filter (\(_, a, _) -> relevance a == Relevant)
               $ snd <$> tele'
    brScope' <- erase $ instantiateTele pureVs brScope
    return (c, tele'', Simple.abstract abstr brScope')
  modifyIndent pred
  tr "eraseBranches res" $ SimpleConBranches cbrs'
  return $ SimpleConBranches cbrs'
eraseBranches (LitBranches lbrs d)
  = SimpleLitBranches
    <$> sequence [(,) l <$> erase e | (l, e) <- lbrs]
    <*> erase d

eraseDef
  :: Definition Abstract.Expr (MetaVar Abstract.Expr)
  -> AbstractM
  -> TCM SLambdaM
eraseDef (Definition e) _ = eraseS e
eraseDef (DataDefinition _) typ = go typ
  where
    go (Abstract.Pi h a t s)
      | relevance a == Relevant = do
        v <- forall h t
        sz <- erase =<< sizeOfType t
        e <- go $ instantiate1 (pure v) s
        return $ SLambda.Sized (SLambda.Lit 1) $ SLambda.Lam h sz $ Simple.abstract1 v e
      | otherwise = do
        v <- forall h t
        go $ instantiate1 (pure v) s
    go _ = return $ SLambda.Sized (SLambda.Lit 0) $ SLambda.Con Builtin.Unit mempty
