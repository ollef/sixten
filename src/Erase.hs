{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Erase where

import qualified Bound.Scope.Simple as Simple
import Bound.Scope
import Control.Monad.Except
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.SLambda as SLambda
import Meta
import TCM
import Unify

eraseS :: AbstractM s -> TCM s (SLambdaM s)
eraseS e = SLambda.Sized <$> (erase =<< sizeOf e) <*> erase e

erase :: AbstractM s -> TCM s (LambdaM s)
erase expr = do
  tr "erase expr" expr
  modifyIndent succ
  res <- case expr of
    Abstract.Var v -> return $ SLambda.Var v
    Abstract.Global g -> return $ SLambda.Global g
    Abstract.Lit l -> return $ SLambda.Lit l
    Abstract.Pi {} -> return $ SLambda.Global "__unit"
    Abstract.Lam h a t s
      | relevance a == Relevant -> do
        v <- forall_ h t
        e <- eraseS $ instantiate1 (pure v) s
        sz <- erase =<< sizeOfType t
        return $ SLambda.Lam h sz $ Simple.abstract1 v e
      | otherwise -> do
        v <- forall_ h t
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

relevantAbstraction :: Telescope expr v -> Tele -> Maybe Tele
relevantAbstraction tele (Tele n) = Tele <$> perm Vector.! n
  where
    perm = Vector.fromList $ reverse $ fst $
      Vector.foldl' (\(xs, i) (_, a, _) -> case relevance a of
          Irrelevant -> (Nothing : xs, i)
          Relevant -> (Just i : xs, i + 1))
        ([], 0) $ unTelescope tele

eraseBranches
  :: Pretty c
  => BranchesM c Abstract.Expr s
  -> TCM s (SimpleBranchesM c SLambda.Expr s)
eraseBranches (ConBranches cbrs typ) = do
  tr "eraseBranches brs" $ ConBranches cbrs typ
  modifyIndent succ
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h a s -> do
      let t = instantiateTele pureVs s
      tsz <- erase =<< sizeOfType t
      v <- forall_ h t
      return (v, (h, a, Simple.abstract abstr tsz))
    let vs = fst <$> tele'
        abstr v = relevantAbstraction tele =<< teleAbstraction vs v
        pureVs = pure <$> vs
        tele'' = SimpleTelescope
               $ fmap (\(h, _, t) -> (h, t))
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
  :: Definition Abstract.Expr Void
  -> TCM s (Definition SLambda.SExpr Void)
eraseDef (Definition e) = fmap (error . show) . Definition <$> eraseS (vacuous e)
eraseDef (DataDefinition DataDef {})
  = return $ DataDefinition $ DataDef mempty
