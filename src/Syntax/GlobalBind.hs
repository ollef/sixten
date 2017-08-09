module Syntax.GlobalBind where

import Bound
import Bound.Var
import Data.Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet

import Syntax.Module

class GlobalBound t where
  -- | Perform substitution on both variables and globals inside a structure.
  bound
    :: GlobalBind e
    => (v -> e v')
    -> (QName -> e v')
    -> t e v
    -> t e v'

instance GlobalBound (Scope b) where
  bound f g (Scope s)
    = Scope
    $ bind
      (unvar (pure . B) $ pure . F . bind f g)
      (pure . F . g)
      s

class Monad e => GlobalBind e where
  global :: QName -> e v
  -- | Perform substitution on both variables and globals.
  bind
    :: (v -> e v')
    -> (QName -> e v')
    -> e v
    -> e v'

boundJoin :: (GlobalBind f, GlobalBound t) => t f (f a) -> t f a
boundJoin = bound id global

globals :: (Foldable e, GlobalBind e) => e v -> HashSet QName
globals = fold . bind (pure . const mempty) (pure . HashSet.singleton)

boundGlobals :: (Foldable (t e), GlobalBind e, GlobalBound t) => t e v -> HashSet QName
boundGlobals = fold . bound (pure . const mempty) (pure . HashSet.singleton)
