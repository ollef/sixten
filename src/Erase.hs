{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Erase where

import Bound.Scope
import Control.Monad.Except
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Void

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Lambda as Lambda
import Meta
import TCM
import Unify

erase :: AbstractM s -> TCM s (LambdaM s)
erase expr = do
  tr "erase expr" expr
  modifyIndent succ
  res <- case expr of
    Abstract.Var v -> return $ Lambda.Var v
    Abstract.Global g -> return $ Lambda.Global g
    Abstract.Lit l -> return $ Lambda.Lit l
    Abstract.Pi {} -> return $ Lambda.Global "__unit"
    Abstract.Lam h a t s
      | relevance a == Relevant -> do
        v <- forall_ h t
        e <- erase $ instantiate1 (pure v) s
        sz <- erase =<< sizeOfType t
        return $ Lambda.Lam h sz $ abstract1 v e
      | otherwise -> do
        v <- forall_ h t
        erase $ instantiate1 (pure v) s
    (appsView -> (Abstract.Con qc, es)) -> do
      n <- constrArity qc
      case compare argsLen n of
        GT -> throwError $ "erase: too many args for constructor: " ++ show qc
        EQ -> Lambda.Con qc <$> mapM (\e -> (,) <$> erase e <*> (erase =<< sizeOf e)) es'
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
      | relevance a == Relevant -> Lambda.App <$> erase e1 <*> erase e2
      | otherwise -> erase e1
    Abstract.Case e brs -> Lambda.Case <$> erase e <*> eraseBranches brs
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
  -> TCM s (BranchesM c Lambda.Expr s)
eraseBranches (ConBranches cbrs typ) = do
  tr "eraseBranches brs" $ ConBranches cbrs typ
  modifyIndent succ
  typSize <- erase =<< sizeOfType typ
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h a s -> do
      let t = instantiateTele pureVs s
      tsz <- erase =<< sizeOfType t
      v <- forall_ h t
      return (v, (h, a, abstract abstr tsz))
    let vs = fst <$> tele'
        abstr v = relevantAbstraction tele =<< teleAbstraction vs v
        pureVs = pure <$> vs
        tele'' = Telescope
               $ Vector.filter (\(_, a, _) -> relevance a == Relevant)
               $ snd <$> tele'
    brScope' <- erase $ instantiateTele pureVs brScope
    return (c, tele'', abstract abstr brScope')
  modifyIndent pred
  tr "eraseBranches res" $ ConBranches cbrs' typSize
  return $ ConBranches cbrs' typSize
eraseBranches (LitBranches lbrs d) = LitBranches <$> sequence [(,) l <$> erase e | (l, e) <- lbrs] <*> erase d

eraseDef
  :: Definition Abstract.Expr Void
  -> TCM s (Definition Lambda.Expr Void)
eraseDef (Definition e) = fmap (error . show) . Definition <$> erase (vacuous e)
eraseDef (DataDefinition DataDef {})
  = return $ DataDefinition $ DataDef mempty
