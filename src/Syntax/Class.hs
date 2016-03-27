{-# LANGUAGE ViewPatterns #-}
module Syntax.Class where
import Bound
import Bound.Scope
import Data.Bifunctor
import Data.Foldable as Foldable

import Syntax.Annotation
import Syntax.Hint
import Syntax.Telescope
import Util

class (Monad e, Traversable e) => Syntax e where
  pi_ :: NameHint -> Annotation -> e v -> Scope1 e v -> e v
  piView, lamView :: e v -> Maybe (NameHint, Annotation, e v, Scope1 e v)
  app :: e v -> Annotation -> e v -> e v
  appView :: e v -> Maybe (e v, Annotation, e v)

apps :: (Syntax e, Foldable t) => e v -> t (Annotation, e v) -> e v
apps = Foldable.foldl (uncurry . app)

appsView :: Syntax e => e v -> (e v, [(Annotation, e v)])
appsView = second reverse . go
  where
    go (appView -> Just (e1, p, e2)) = second ((p, e2) :) $ go e1
    go e = (e, [])

usedPiView
  :: Syntax e
  => e v
  -> Maybe (NameHint, Annotation, e v, Scope1 e v)
usedPiView (piView -> Just (n, p, e, s@(unusedScope -> Nothing))) = Just (n, p, e, s)
usedPiView _ = Nothing

telescope :: Syntax e => e v -> Telescope e v
telescope (pisView -> (tele, _)) = tele

pisView :: Syntax e => e v -> (Telescope e v, Scope Tele e v)
pisView = bindingsView piView

betaApp :: Syntax e => e v -> Annotation -> e v -> e v
betaApp e1@(lamView -> Just (_, p1, _, s)) p2 e2 | p1 == p2 = case bindings s of
  []  -> instantiate1 e2 s
  [_] -> instantiate1 e2 s
  _   -> app e1 p1 e2
betaApp e1 p e2 = app e1 p e2

arrow :: Syntax e => Annotation -> e v -> e v -> e v
arrow p a b = pi_ (Hint Nothing) p a $ Scope $ pure $ F b
