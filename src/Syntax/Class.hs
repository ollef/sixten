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

class (Monad e, Traversable e) => SyntaxLambda e where
  lam :: NameHint -> Annotation -> e v -> Scope1 e v -> e v
  lamView :: e v -> Maybe (NameHint, Annotation, e v, Scope1 e v)

class (Monad e, Traversable e) => SyntaxPi e where
  pi_ :: NameHint -> Annotation -> e v -> Scope1 e v -> e v
  piView :: e v -> Maybe (NameHint, Annotation, e v, Scope1 e v)

class (Monad e, Traversable e) => SyntaxApp e where
  app :: e v -> Annotation -> e v -> e v
  appView :: e v -> Maybe (e v, Annotation, e v)

class (SyntaxLambda e, SyntaxPi e, SyntaxApp e) => Syntax e where

apps :: (SyntaxApp e, Foldable t) => e v -> t (Annotation, e v) -> e v
apps = Foldable.foldl (uncurry . app)

appsView :: SyntaxApp e => e v -> (e v, [(Annotation, e v)])
appsView = second reverse . go
  where
    go (appView -> Just (e1, p, e2)) = second ((p, e2) :) $ go e1
    go e = (e, [])

typeApp :: SyntaxPi e => e v -> e v -> Maybe (e v)
typeApp (piView -> Just (_, _, _, s)) e = Just $ instantiate1 e s
typeApp _ _ = Nothing

typeApps :: (SyntaxPi e, Foldable t) => e v -> t (e v) -> Maybe (e v)
typeApps = foldlM typeApp

usedPiView
  :: SyntaxPi e
  => e v
  -> Maybe (NameHint, Annotation, e v, Scope1 e v)
usedPiView (piView -> Just (n, p, e, s@(unusedScope -> Nothing))) = Just (n, p, e, s)
usedPiView _ = Nothing

usedPisViewM :: SyntaxPi e => e v -> Maybe (Telescope Scope Annotation e v, Scope Tele e v)
usedPisViewM = bindingsViewM usedPiView

telescope :: SyntaxPi e => e v -> Telescope Scope Annotation e v
telescope (pisView -> (tele, _)) = tele

pisView :: SyntaxPi e => e v -> (Telescope Scope Annotation e v, Scope Tele e v)
pisView = bindingsView piView

pisViewM :: SyntaxPi e => e v -> Maybe (Telescope Scope Annotation e v, Scope Tele e v)
pisViewM = bindingsViewM piView

lamsView :: SyntaxLambda e => e v -> (Telescope Scope Annotation e v, Scope Tele e v)
lamsView = bindingsView lamView

lamsViewM :: SyntaxLambda e => e v -> Maybe (Telescope Scope Annotation e v, Scope Tele e v)
lamsViewM = bindingsViewM lamView

lams :: (SyntaxLambda e, Eq v) => Telescope Scope Annotation e v -> Scope Tele e v -> e v
lams tele s = quantify lam s tele

pis :: (SyntaxPi e, Eq v) => Telescope Scope Annotation e v -> Scope Tele e v -> e v
pis tele s = quantify pi_ s tele

betaApp :: (SyntaxApp e, SyntaxLambda e) => e v -> Annotation -> e v -> e v
betaApp e1@(lamView -> Just (_, p1, _, s)) p2 e2 | p1 == p2 = case bindings s of
  []  -> instantiate1 e2 s
  [_] -> instantiate1 e2 s
  _   -> app e1 p1 e2
betaApp e1 p e2 = app e1 p e2

betaApps :: (SyntaxApp e, SyntaxLambda e, Foldable t) => e v -> t (Annotation, e v) -> e v
betaApps = Foldable.foldl (uncurry . betaApp)

arrow :: SyntaxPi e => Annotation -> e v -> e v -> e v
arrow p a b = pi_ mempty p a $ Scope $ pure $ F b
