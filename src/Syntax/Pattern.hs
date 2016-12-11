{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Pattern where

import Bound
import Control.Monad.State
import Data.Bitraversable
import Data.Functor.Identity
import Data.Maybe
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Util hiding (indexed)

type PatternScope = Scope PatternVar
newtype PatternVar = PatternVar Int
  deriving (Eq, Ord, Show, Num)

unPatternVar :: PatternVar -> Int
unPatternVar (PatternVar i) = i

patternAbstraction
  :: Eq b
  => Vector b
  -> b
  -> Maybe PatternVar
patternAbstraction vs = fmap PatternVar . (`Vector.elemIndex` vs)

abstractPatternsTypes
  :: (Bitraversable pat, Eq v, Monad typ, Traversable t)
  => Vector v
  -> t (p, pat (typ v) b)
  -> t (p, pat (PatternScope typ v) b)
abstractPatternsTypes vars
  = flip evalState 0 . traverse (bitraverse pure (bitraverse (abstractType vars) inc))
  where
    abstractType
      :: (Eq v, Monad typ)
      => Vector v
      -> typ v
      -> State Int (Scope PatternVar typ v)
    abstractType vs typ = do
      prefix <- get
      let abstr v = case Vector.elemIndex v vs of
            Just i | i < prefix -> Just $ PatternVar i
            _ -> Nothing
      return $ abstract abstr typ

    inc b = do
      n <- get
      put $! n + 1
      pure b

abstractPatternTypes
  :: (Bitraversable pat, Eq v, Monad typ)
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

instantiatePattern
  :: (Monad f, Foldable pat)
  => (v -> f v')
  -> pat v
  -> Scope PatternVar f v'
  -> f v'
instantiatePattern f pat = instantiatePatternVec f $ toVector pat

instantiatePatternVec
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope PatternVar f a
  -> f a
instantiatePatternVec f vs
  = instantiate (f . fromMaybe (error "instantiatePatternVec") . (vs Vector.!?) . unPatternVar)
