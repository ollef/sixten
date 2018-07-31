{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Pattern where

import Bound
import Control.Monad.State.Strict
import Data.Bitraversable
import Data.Functor.Identity
import Data.Hashable
import Data.Maybe
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Util

type PatternScope = Scope PatternVar
newtype PatternVar = PatternVar Int
  deriving (Eq, Ord, Show, Num)

unPatternVar :: PatternVar -> Int
unPatternVar (PatternVar i) = i

patternAbstraction
  :: (Eq b, Hashable b)
  => Vector b
  -> b
  -> Maybe PatternVar
patternAbstraction vs = fmap PatternVar . hashedElemIndex vs

abstractPatternsTypes
  :: (Bitraversable pat, Eq v, Hashable v, Monad typ, Traversable t)
  => Vector v
  -> t (p, pat (typ v) b)
  -> t (p, pat (PatternScope typ v) b)
abstractPatternsTypes vars
  = flip evalState 0 . traverse (bitraverse pure (bitraverse (abstractType vars) inc))
  where
    abstractType
      :: (Eq v, Hashable v, Monad typ)
      => Vector v
      -> typ v
      -> State Int (Scope PatternVar typ v)
    abstractType vs typ = do
      prefix <- get
      let abstr v = case hashedElemIndex vs v of
            Just i | i < prefix -> Just $ PatternVar i
            _ -> Nothing
      return $ abstract abstr typ

    inc b = do
      n <- get
      put $! n + 1
      pure b

abstractPatternTypes
  :: (Bitraversable pat, Eq v, Hashable v, Monad typ)
  => Vector v
  -> pat (typ v) b
  -> pat (PatternScope typ v) b
abstractPatternTypes vars
  = snd
  . runIdentity
  . abstractPatternsTypes vars
  . Identity
  . (,) ()

indexedPattern
  :: Traversable pat
  => pat b
  -> pat (PatternVar, b)
indexedPattern = flip evalState 0 . traverse inc
  where
    inc b = do
      n <- get
      put $! n + 1
      pure (n, b)

indexedPatterns
  :: (Traversable f, Traversable pat)
  => f (p, pat b)
  -> f (p, pat (PatternVar, b))
indexedPatterns = flip evalState 0 . traverse (traverse $ traverse inc)
  where
    inc b = do
      n <- get
      put $! n + 1
      pure (n, b)

renamePatterns
  :: (Traversable f, Traversable pat)
  => Vector v
  -> f (p, pat b)
  -> f (p, pat v)
renamePatterns vs pats
  = fmap (fmap (\(v, _) -> vs Vector.! unPatternVar v)) <$> indexedPatterns pats

instantiatePattern
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope PatternVar f a
  -> f a
instantiatePattern f vs
  = instantiate (f . fromMaybe (error "instantiatePattern") . (vs Vector.!?) . unPatternVar)
