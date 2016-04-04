{-# LANGUAGE OverloadedStrings, RecursiveDo  #-}
module Erase where

import Bound.Scope
import Data.Traversable
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Lambda as Lambda
import Meta
import Util
import TCM
import Unify

erase :: AbstractM s -> TCM s (LambdaM s)
erase expr = do
  tr "erase expr" expr
  modifyIndent succ
  res <- case expr of
    Abstract.Var v -> return $ Lambda.Var v
    Abstract.Global g -> return $ Lambda.Global g
    Abstract.Con c -> return $ Lambda.Con c
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
    tele' <- forTele tele $ \h a s -> do
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
  :: Definition Abstract.Expr Empty
  -> TCM s (Definition Lambda.Expr Empty)
eraseDef (Definition e) = fmap (error . show) . Definition <$> erase (fromEmpty <$> e)
eraseDef (DataDefinition DataDef {})
  = return $ DataDefinition $ DataDef mempty
