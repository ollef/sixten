{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.Unify.Indices where

import Protolude

import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashSet as HashSet

import qualified Elaboration.Equal as Equal
import Elaboration.Monad
import Elaboration.Normalise
import Syntax
import Syntax.Core
import Util

data Result a
  = Nope
  | Dunno
  | Success a
  deriving (Eq, Ord, Show, Functor)

instance Semigroup a => Semigroup (Result a) where
  Nope <> _ = Nope
  _ <> Nope = Nope
  Dunno <> _ = Dunno
  _ <> Dunno = Dunno
  Success a <> Success b = Success $ a <>  b

instance Monoid a => Monoid (Result a) where
  mempty = Success mempty

type Subst = HashMap FreeVar CoreM

unify :: CoreM -> CoreM -> Elaborate (Result Subst)
unify expr1 expr2 = do
  expr1' <- whnf expr1
  expr2' <- whnf expr2
  unify' expr1' expr2'

unify' :: CoreM -> CoreM -> Elaborate (Result Subst)
unify' expr1 expr2 = case (expr1, expr2) of
  (Var v1, Var v2)
    | v1 == v2 -> return mempty
  (Var v1, _)
    | not $ v1 `HashSet.member` toHashSet expr2 ->
      return $ Success $ HashMap.singleton v1 expr2
  (_, Var v2)
    | not $ v2 `HashSet.member` toHashSet expr1 ->
      return $ Success $ HashMap.singleton v2 expr1
  (appsView -> (unSourceLoc -> Con c1, es1), appsView -> (unSourceLoc -> Con c2, es2))
    | c1 == c2 -> do
      when (length es1 /= length es2) $
        panic "Indices.unify: mismatched lengths"
      substs <- zipWithM (unify `on` snd) es1 es2
      return $ fold substs
    | otherwise -> return Nope
  (Lit l1, Lit l2)
    | l1 == l2 -> return mempty
    | otherwise -> return Nope
  _ -> do
    equal <- Equal.exec $ Equal.expr expr1 expr2
    return $
      if equal then
        mempty
      else
        Dunno
