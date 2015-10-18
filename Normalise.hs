{-# LANGUAGE ViewPatterns #-}
module Normalise where

import Bound
import Control.Monad.Except
import Data.Bifunctor
import Data.Hashable

import Annotation
import Core
import qualified Input
import Meta
import Monad

whnf :: (Eq v, Hashable v, Show v, HasPlicitness a)
     => (a -> d) -> (Annotation -> a) -> CoreM s d a v -> TCM s v (CoreM s d a v)
whnf dat anno expr = case expr of
  Var (F (metaRef -> Nothing)) -> return expr
  Var (F (metaRef -> Just r)) -> refineIfSolved r expr (whnf dat anno)
  Var (F _) -> throwError "whnf impossible"
  Var (B v) -> do
    (d, _, _) <- context v
    case d of
      Input.Definition e -> whnf dat anno $ bimap anno B e
      _ -> return expr
  Con _ -> return expr
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
  Case _ _ -> undefined -- TODO

normalise :: (Eq a, Eq v, Hashable v, Show d, Show v, Show a, HasPlicitness a)
          => d -> (Annotation -> a) -> CoreM s d a v -> TCM s v (CoreM s d a v)
normalise dat anno expr = case expr of
  Var (F (metaRef -> Nothing)) -> return expr
  Var (F (metaRef -> Just r)) -> refineIfSolved r expr (normalise dat anno)
  Var (F _) -> throwError "normalise impossible"
  Var (B v) -> do
    (d, _, _) <- context v
    case d of
      Input.Definition e -> normalise dat anno $ bimap anno B e
      _ -> return expr
  Con _ -> return expr
  Type -> return expr
  Pi n p a s -> normaliseScope n (Pi n p)  a s
  Lam n p a s -> normaliseScope n (Lam n p) a s
  App e1 p e2 -> do
    e1' <- normalise dat anno e1
    e2' <- normalise dat anno e2
    case e1' of
      Lam _ p' _ s | plicitness p == plicitness p'   -> normalise dat anno $ instantiate1 e2' s
      _ -> return $ App e1' p e2'
  Case _ _ -> undefined -- TODO
  where
    normaliseScope h c a s = do
      x <- forall_ h a dat
      ns <- normalise dat anno $ instantiate1 (return $ F x) s
      c a <$> abstract1M x ns
