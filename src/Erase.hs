{-# LANGUAGE OverloadedStrings, RecursiveDo, ViewPatterns #-}
module Erase where

import Bound.Scope
import Control.Monad.Except
import Data.Monoid
import qualified Data.Vector as Vector

import qualified Builtin
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.SLambda as SLambda
import Meta
import TypeOf
import TCM

eraseS :: AbstractE -> TCM LambdaM
eraseS e = SLambda.Sized <$> (erase =<< sizeOf e) <*> erase e

erase :: AbstractE -> TCM LambdaM
erase expr = do
  logMeta 20 "erase expr" expr
  modifyIndent succ
  res <- case expr of
    Abstract.Var v -> return $ SLambda.Var v
    Abstract.Global g -> return $ SLambda.Global g
    Abstract.Lit l -> return $ SLambda.Lit l
    Abstract.Pi {} -> return $ SLambda.Con Builtin.Unit mempty
    Abstract.Lam h Erased t s -> do
      v <- forall h Erased t
      erase $ instantiate1 (pure v) s
    Abstract.Lam h Retained t s -> do
      v <- forall h Retained t
      e <- eraseS $ instantiate1 (pure v) s
      sz <- erase =<< sizeOfType t
      return $ SLambda.Lam h sz $ abstract1 v e
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
        es' = Vector.fromList $ snd <$> filter (\(a, _) -> a == Retained) es
        argsLen = length es
    Abstract.Con _qc -> throwError "erase impossible"
    Abstract.App e1 Retained e2 -> SLambda.App <$> erase e1 <*> eraseS e2
    Abstract.App e1 Erased _e2 -> erase e1
    Abstract.Case e brs -> SLambda.Case <$> eraseS e <*> eraseBranches brs
  modifyIndent pred
  logMeta 20 "erase res" res
  return res

retainedAbstraction :: Telescope Erasability expr v -> Tele -> Maybe Tele
retainedAbstraction tele (Tele n) = Tele <$> perm Vector.! n
  where
    perm = Vector.fromList $ reverse $ fst $
      Vector.foldl' (\(xs, i) (_, a, _) -> case a of
          Erased -> (Nothing : xs, i)
          Retained -> (Just i : xs, i + 1))
        ([], 0) $ unTelescope tele

eraseBranches
  :: Pretty c
  => Branches c Erasability Abstract.ExprE (MetaVar Abstract.ExprE)
  -> TCM (Branches c () SLambda.Expr (MetaVar Abstract.ExprE))
eraseBranches (ConBranches cbrs typ) = do
  logMeta 20 "eraseBranches brs" $ ConBranches cbrs typ
  resultSize <- erase =<< sizeOfType typ
  modifyIndent succ
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h a s -> do
      let t = instantiateTele pureVs s
      tsz <- erase =<< sizeOfType t
      v <- forall h a t
      return (v, (h, a, abstract abstr tsz))
    let vs = fst <$> tele'
        abstr v = retainedAbstraction tele =<< teleAbstraction vs v
        pureVs = pure <$> vs
        tele'' = Telescope
               $ fmap (\(h, _, t) -> (h, (), t))
               $ Vector.filter (\(_, a, _) -> a == Retained)
               $ snd <$> tele'
    brScope' <- erase $ instantiateTele pureVs brScope
    return (c, tele'', abstract abstr brScope')
  modifyIndent pred
  logMeta 20 "eraseBranches res" $ ConBranches cbrs' resultSize
  return $ ConBranches cbrs' resultSize
eraseBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [(,) l <$> erase e | (l, e) <- lbrs]
    <*> erase d

eraseDef
  :: Definition Abstract.ExprE (MetaVar Abstract.ExprE)
  -> AbstractE
  -> TCM LambdaM
eraseDef (Definition e) _ = eraseS e
eraseDef (DataDefinition _) typ = go typ
  where
    go (Abstract.Pi h Retained t s) = do
      v <- forall h Retained t
      sz <- erase =<< sizeOfType t
      e <- go $ instantiate1 (pure v) s
      return $ SLambda.Sized (SLambda.Lit 1) $ SLambda.Lam h sz $ abstract1 v e
    go (Abstract.Pi h Erased t s) = do
      v <- forall h Erased t
      go $ instantiate1 (pure v) s
    go _ = return $ SLambda.Sized (SLambda.Lit 0) $ SLambda.Con Builtin.Unit mempty
