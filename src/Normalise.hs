{-# LANGUAGE ViewPatterns #-}
module Normalise where

import Control.Monad.Except

import qualified Builtin
import qualified Context
import Meta
import TCM
import Syntax
import Syntax.Abstract
import Util

whnf :: AbstractM s -> TCM s (AbstractM s)
whnf expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r) -> refineIfSolved r expr whnf
  Var _ -> throwError "whnf impossible"
  Global v -> do
    (d, _) <- Context.definition v
    case d of
      Definition e -> whnf e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi {} -> return expr
  Lam {} -> return expr
  Builtin.AddSize x y -> binOp 0 (+) Builtin.AddSize x y
  Builtin.MaxSize x y -> binOp 0 max Builtin.MaxSize x y
  App e1 p e2 -> do
    e1' <- whnf e1
    case e1' of
      Lam h p' t2 s | p == p' -> do
        e2' <- letVar h e2 t2
        whnf $ instantiate1 e2' s
      _ -> return expr
  Case _ _ -> return expr -- TODO

normalise :: AbstractM s -> TCM s (AbstractM s)
normalise expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r) -> refineIfSolved r expr normalise
  Var _ -> throwError "normalise impossible"
  Global v -> do
    (d, _) <- Context.definition v
    case d of
      Definition e -> normalise e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi n p a s -> normaliseScope n (Pi n p)  a s
  Lam n p a s -> normaliseScope n (Lam n p) a s
  Builtin.AddSize x y -> binOp 0 (+) Builtin.AddSize x y
  Builtin.MaxSize x y -> binOp 0 max Builtin.MaxSize x y
  App e1 p e2 -> do
    e1' <- normalise e1
    e2' <- normalise e2
    case e1' of
      Lam _ p' _ s | p == p' -> normalise $ instantiate1 e2' s
      _ -> return $ App e1' p e2'
  Case _ _ -> return expr -- TODO
  where
    normaliseScope h c a s = do
      x <- forall_ h a
      ns <- normalise $ instantiate1 (pure x) s
      c a <$> abstract1M x ns

binOp
  :: Literal
  -> (Literal -> Literal -> Literal)
  -> (AbstractM s -> AbstractM s -> AbstractM s)
  -> AbstractM s
  -> AbstractM s
  -> TCM s (AbstractM s)
binOp zero op cop x y = do
    x' <- normalise x
    y' <- normalise y
    case (x', y') of
      (Lit m, _) | m == zero -> return y'
      (_, Lit n) | n == zero -> return x'
      (Lit m, Lit n) -> return $ Lit $ op m n
      _ -> return $ cop x' y'
