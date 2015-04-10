{-# LANGUAGE ViewPatterns #-}
module Normalise where

import Bound
import Control.Monad.Except

import Core
import Meta
import Monad

whnf :: Core s -> TCM s (Core s)
whnf expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r)  -> refineIfSolved r expr whnf
  Var _                    -> throwError "whnf impossible"
  Type                     -> return expr
  Pi {}                    -> return expr
  Lam {}                   -> return expr
  App e1 p e2              -> do
    e1' <- whnf e1
    case e1' of
      Lam h p' t2 s | p == p' -> do
        e2' <- freshLetV h e2 t2
        whnf $ instantiate1 e2' s
      _ -> return expr
  Case _ _ -> undefined -- TODO

normalise :: Core s -> TCM s (Core s)
normalise expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r)  -> refineIfSolved r expr normalise
  Var _                    -> throwError "normalise impossible"
  Type                     -> return expr
  Pi n p a s               -> normaliseScope n (Pi n p)  a s
  Lam n p a s              -> normaliseScope n (Lam n p) a s
  App e1 p e2              -> do
    e1' <- normalise e1
    e2' <- normalise e2
    case e1' of
      Lam _ p' _ s | p == p' -> normalise $ instantiate1 e2' s
      _                           -> return $ App e1' p e2'
  Case _ _ -> undefined -- TODO
  where
    normaliseScope h c a s = do
      x <- freshForall h a
      ns <- normalise $ instantiate1 (return x) s
      c a <$> abstract1M x ns
