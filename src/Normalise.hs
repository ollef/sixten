{-# LANGUAGE ViewPatterns #-}
module Normalise where

import Control.Monad.Except
import Data.Bifunctor

import Meta
import TCM
import Syntax
import Syntax.Abstract

whnf :: HasPlicitness a
     => (a -> d) -> (Annotation -> a) -> AbstractM s d a -> TCM s (AbstractM s d a)
whnf dat anno expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r) -> refineIfSolved r expr (whnf dat anno)
  Var _ -> throwError "whnf impossible"
  Global v -> do
    (d, _, _) <- context v
    case d of
      Definition e -> whnf dat anno $ first anno e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Type -> return expr
  Pi {} -> return expr
  Lam {} -> return expr
  App e1 p e2 -> do
    e1' <- whnf dat anno e1
    case e1' of
      Lam h p' t2 s | plicitness p == plicitness p' -> do
        e2' <- letVar h e2 t2 (dat p)
        whnf dat anno $ instantiate1 e2' s
      _ -> return expr
  Case _ _ -> return expr -- TODO

normalise :: (Eq a, Show d, Show a, HasPlicitness a)
          => d -> (Annotation -> a) -> AbstractM s d a -> TCM s (AbstractM s d a)
normalise dat anno expr = case expr of
  Var (metaRef -> Nothing) -> return expr
  Var (metaRef -> Just r) -> refineIfSolved r expr (normalise dat anno)
  Var _ -> throwError "normalise impossible"
  Global v -> do
    (d, _, _) <- context v
    case d of
      Definition e -> normalise dat anno $ first anno e
      _ -> return expr
  Con _ -> return expr
  Lit _ -> return expr
  Type -> return expr
  Pi n p a s -> normaliseScope n (Pi n p)  a s
  Lam n p a s -> normaliseScope n (Lam n p) a s
  App e1 p e2 -> do
    e1' <- normalise dat anno e1
    e2' <- normalise dat anno e2
    case e1' of
      Lam _ p' _ s | plicitness p == plicitness p'   -> normalise dat anno $ instantiate1 e2' s
      _ -> return $ App e1' p e2'
  Case _ _ -> return expr -- TODO
  where
    normaliseScope h c a s = do
      x <- forall_ h a dat
      ns <- normalise dat anno $ instantiate1 (pure x) s
      c a <$> abstract1M x ns
