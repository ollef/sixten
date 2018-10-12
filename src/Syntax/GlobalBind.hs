module Syntax.GlobalBind where

import Protolude

import Bound
import Bound.Var
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet

import Syntax.QName

class Bound t => GBound t where
  -- | Perform substitution on globals inside a structure.
  gbound :: GBind e => (QName -> e v) -> t e v -> t e v

class Monad e => GBind e where
  global :: QName -> e v
  -- | Perform substitution on globals.
  gbind :: (QName -> e v) -> e v -> e v

instance GBound (Scope b) where
  gbound f (Scope s)
    = Scope $ gbind (pure . F . f) $ fmap (gbind f) <$> s

boundJoin :: (Monad f, Bound t) => t f (f a) -> t f a
boundJoin = (>>>= identity)

globals :: (Foldable e, GBind e) => e v -> HashSet QName
globals = fold . gbind (pure . HashSet.singleton) . fmap (const mempty)

boundGlobals
  :: (Functor (t e), Foldable (t e), GBind e, GBound t)
  => t e v
  -> HashSet QName
boundGlobals = fold . gbound (pure . HashSet.singleton) . fmap (const mempty)

traverseGlobals
  :: (GBound t, GBind e, Traversable (t e), Applicative f)
  => (QName -> f QName)
  -> t e a
  -> f (t e a)
traverseGlobals f
  = fmap (>>>= unvar pure global)
  . sequenceA
  . gbound (pure . fmap F . f)
  . fmap (pure . B)
