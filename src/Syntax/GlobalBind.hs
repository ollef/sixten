{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Syntax.GlobalBind where

import Protolude

import Bound
import Bound.Var
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet

class Bound t => GBound t where
  -- | Perform substitution on globals inside a structure.
  gbound :: GBind e g => (g -> e v) -> t e v -> t e v

class Monad e => GBind e g | e -> g where
  global :: g -> e v
  -- | Perform substitution on globals.
  gbind :: (g -> e v) -> e v -> e v

instance GBound (Scope b) where
  gbound f (Scope s)
    = Scope $ gbind (pure . F . f) $ fmap (gbind f) <$> s

boundJoin :: (Monad f, Bound t) => t f (f a) -> t f a
boundJoin = (>>>= identity)

globals :: (Foldable e, GBind e g, Hashable g, Eq g) => e v -> HashSet g
globals = fold . gbind (pure . HashSet.singleton) . fmap (const mempty)

boundGlobals
  :: (Functor (t e), Foldable (t e), GBind e g, GBound t, Hashable g, Eq g)
  => t e v
  -> HashSet g
boundGlobals = fold . gbound (pure . HashSet.singleton) . fmap (const mempty)

traverseGlobals
  :: (GBound t, GBind e g, Traversable (t e), Applicative f)
  => (g -> f g)
  -> t e a
  -> f (t e a)
traverseGlobals f
  = fmap (>>>= unvar pure global)
  . sequenceA
  . gbound (pure . fmap F . f)
  . fmap (pure . B)
