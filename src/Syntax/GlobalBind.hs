module Syntax.GlobalBind where

import Bound
import Bound.Var
import Syntax.Name

class GlobalBound t where
  -- | Perform substitution on both variables and globals inside a structure.
  bound
    :: GlobalBind e
    => (v -> e v')
    -> (Name -> e v')
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
  global :: Name -> e v
  -- | Perform substitution on both variables and globals.
  bind
    :: (v -> e v')
    -> (Name -> e v')
    -> e v
    -> e v'

boundJoin :: (GlobalBind f, GlobalBound t) => t f (f a) -> t f a
boundJoin = bound id global
