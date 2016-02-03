{-# LANGUAGE ViewPatterns #-}
module Normalise where

import Control.Monad.Except

import qualified Builtin
import Meta
import TCM
import Syntax
import Syntax.Abstract

whnf :: AbstractM s -> TCM s (AbstractM s)
whnf expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r) -> refineIfSolved r expr whnf
  Var _ -> throwError "whnf impossible"
  Global v -> do
    (d, _) <- context v
    case d of
      Definition e -> whnf e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi {} -> return expr
  Lam {} -> return expr
  Builtin.AddSize x y -> do
    x' <- whnf x
    y' <- whnf y
    case (x', y') of
      (Lit 0, _) -> return y'
      (_, Lit 0) -> return x'
      (Lit m, Lit n) -> return $ Lit $ m + n
      _ -> return $ Builtin.AddSize x y
  Builtin.MaxSize x y -> do
    x' <- whnf x
    y' <- whnf y
    case (x', y') of
      (Lit 0, _) -> return $ Lit 0
      (_, Lit 0) -> return $ Lit 0
      (Lit m, Lit n) -> return $ Lit $ max m n
      _ -> return $ Builtin.MaxSize x' y'
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
    (d, _) <- context v
    case d of
      Definition e -> normalise e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Pi n p a s -> normaliseScope n (Pi n p)  a s
  Lam n p a s -> normaliseScope n (Lam n p) a s
  Builtin.AddSize x y -> do
    x' <- whnf x
    y' <- whnf y
    case (x', y') of
      (Lit 0, _) -> return y'
      (_, Lit 0) -> return x'
      (Lit m, Lit n) -> return $ Lit $ m + n
      _ -> return $ Builtin.AddSize x y
  Builtin.MaxSize x y -> do
    x' <- whnf x
    y' <- whnf y
    case (x', y') of
      (Lit 0, _) -> return $ Lit 0
      (_, Lit 0) -> return $ Lit 0
      (Lit m, Lit n) -> return $ Lit $ max m n
      _ -> return $ Builtin.MaxSize x' y'
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
