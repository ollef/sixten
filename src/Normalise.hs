{-# LANGUAGE RecursiveDo, ViewPatterns #-}
module Normalise where

import Control.Monad.Except
import qualified Data.Vector as Vector

import qualified Builtin
import Meta
import TCM
import Syntax
import Syntax.Abstract
import Util

whnf :: AbstractM -> TCM AbstractM
whnf expr = do
  -- tr "whnf e" expr
  modifyIndent succ
  res <- case expr of
    Var (metaRef -> Nothing) -> return expr
    Var (metaRef -> Just r) -> refineIfSolved r expr whnf
    Var _ -> throwError "whnf impossible"
    Global v -> do
      (d, _) <- definition v
      case d of
        Definition e -> whnf e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi {} -> return expr
    Lam {} -> return expr
    Builtin.AddSize x y -> binOp 0 (+) Builtin.AddSize whnf x y
    Builtin.MaxSize x y -> binOp 0 max Builtin.MaxSize whnf x y
    App e1 p e2 -> do
      e1' <- whnf e1
      case e1' of
        Lam _ p' _ s | p == p' -> do
          e2' <- whnf e2
          whnf $ instantiate1 e2' s
        _ -> return expr
    Case e brs -> do
      e' <- whnf e
      chooseBranch e' brs whnf
  modifyIndent pred
  -- tr "whnf res" res
  return res

normalise :: AbstractM -> TCM AbstractM
normalise expr = do
  -- tr "normalise e" expr
  modifyIndent succ
  res <- case expr of
    Var (metaRef -> Nothing) -> return expr
    Var (metaRef -> Just r) -> refineIfSolved r expr normalise
    Var _ -> throwError "normalise impossible"
    Global v -> do
      (d, _) <- definition v
      case d of
        Definition e -> normalise e
        _ -> return expr
    Con _ -> return expr
    Lit _ -> return expr
    Pi n p a s -> normaliseScope n (Pi n p)  a s
    Lam n p a s -> normaliseScope n (Lam n p) a s
    Builtin.AddSize x y -> binOp 0 (+) Builtin.AddSize normalise x y
    Builtin.MaxSize x y -> binOp 0 max Builtin.MaxSize normalise x y
    App e1 p e2 -> do
      e1' <- normalise e1
      e2' <- normalise e2
      case e1' of
        Lam _ p' _ s | p == p' -> normalise $ instantiate1 e2' s
        _ -> return $ App e1' p e2'
    Case e brs -> do
      e' <- whnf e
      res <- chooseBranch e' brs whnf
      case res of
        Case e'' brs' -> Case e'' <$> case brs' of
          ConBranches cbrs typ -> ConBranches
            <$> sequence
              [ uncurry ((,,) qc) <$> normaliseTelescope tele s
              | (qc, tele, s) <- cbrs
              ]
            <*> normalise typ
          LitBranches lbrs def -> LitBranches
            <$> sequence [(,) l <$> normalise br | (l, br) <- lbrs]
            <*> normalise def
        _ -> return res
  modifyIndent pred
  -- tr "normalise res" res
  return res
  where
    normaliseTelescope tele scope = mdo
      avs <- forMTele tele $ \h a s -> do
        t' <- normalise $ instantiateTele pvs s
        v <- forall h t'
        return (a, v)
      let vs = snd <$> avs
          pvs = pure <$> vs

          abstr = teleAbstraction vs
      e' <- normalise $ instantiateTele pvs scope
      scope' <- abstractM abstr e'
      tele' <- forM avs $ \(a, v) -> do
        s <- abstractM abstr $ metaType v
        return (metaHint v, a, s)
      return (Telescope tele', scope')
    normaliseScope h c t s = do
      t' <- normalise t
      x <- forall h t'
      ns <- normalise $ instantiate1 (pure x) s
      c t' <$> abstract1M x ns

binOp
  :: Literal
  -> (Literal -> Literal -> Literal)
  -> (AbstractM -> AbstractM -> AbstractM)
  -> (AbstractM -> TCM AbstractM)
  -> AbstractM
  -> AbstractM
  -> TCM AbstractM
binOp zero op cop norm x y = do
    x' <- norm x
    y' <- norm y
    case (x', y') of
      (Lit m, _) | m == zero -> return y'
      (_, Lit n) | n == zero -> return x'
      (Lit m, Lit n) -> return $ Lit $ op m n
      _ -> return $ cop x' y'

chooseBranch
  :: AbstractM
  -> BranchesM QConstr Expr
  -> (AbstractM -> TCM AbstractM)
  -> TCM AbstractM
chooseBranch (Lit l) (LitBranches lbrs def) k = k chosenBranch
  where
    chosenBranch = head $ [br | (l', br) <- lbrs, l == l'] ++ [def]
chooseBranch (appsView -> (Con qc, args)) (ConBranches cbrs _) k =
  k $ instantiateTele (Vector.fromList $ snd <$> args) chosenBranch
  where
    chosenBranch = case [br | (qc', _, br) <- cbrs, qc == qc'] of
      [br] -> br
      _ -> error "Normalise.chooseBranch"
chooseBranch e brs _ = return $ Case e brs
