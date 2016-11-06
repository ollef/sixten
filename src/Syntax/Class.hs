{-# LANGUAGE TypeFamilies, ViewPatterns #-}
module Syntax.Class where
import Bound
import Data.Bifunctor
import Data.Foldable as Foldable

import Syntax.Hint
import Syntax.Telescope
import Util

class (Monad e, Traversable e) => Syntax e where
  type Annotation e

  lam :: NameHint -> Annotation e -> e v -> Scope1 e v -> e v
  lamView :: e v -> Maybe (NameHint, Annotation e, e v, Scope1 e v)

  pi_ :: NameHint -> Annotation e -> e v -> Scope1 e v -> e v
  piView :: e v -> Maybe (NameHint, Annotation e, e v, Scope1 e v)

  app :: e v -> Annotation e -> e v -> e v
  appView :: e v -> Maybe (e v, Annotation e, e v)

apps :: (Syntax e, Foldable t) => e v -> t (Annotation e, e v) -> e v
apps = Foldable.foldl (uncurry . app)

appsView :: Syntax e => e v -> (e v, [(Annotation e, e v)])
appsView = second reverse . go
  where
    go (appView -> Just (e1, p, e2)) = second ((p, e2) :) $ go e1
    go e = (e, [])

typeApp :: Syntax e => e v -> e v -> Maybe (e v)
typeApp (piView -> Just (_, _, _, s)) e = Just $ instantiate1 e s
typeApp _ _ = Nothing

typeApps :: (Syntax e, Foldable t) => e v -> t (e v) -> Maybe (e v)
typeApps = foldlM typeApp

usedPiView
  :: Syntax e
  => e v
  -> Maybe (NameHint, Annotation e, e v, Scope1 e v)
usedPiView (piView -> Just (n, p, e, s@(unusedScope -> Nothing))) = Just (n, p, e, s)
usedPiView _ = Nothing

usedPisViewM :: Syntax e => e v -> Maybe (Telescope (Annotation e) e v, Scope Tele e v)
usedPisViewM = bindingsViewM usedPiView

telescope :: Syntax e => e v -> Telescope (Annotation e) e v
telescope (pisView -> (tele, _)) = tele

pisView :: Syntax e => e v -> (Telescope (Annotation e) e v, Scope Tele e v)
pisView = bindingsView piView

pisViewM :: Syntax e => e v -> Maybe (Telescope (Annotation e) e v, Scope Tele e v)
pisViewM = bindingsViewM piView

lamsView :: Syntax e => e v -> (Telescope (Annotation e) e v, Scope Tele e v)
lamsView = bindingsView lamView

lamsViewM :: Syntax e => e v -> Maybe (Telescope (Annotation e) e v, Scope Tele e v)
lamsViewM = bindingsViewM lamView

lams :: Syntax e => Telescope (Annotation e) e v -> Scope Tele e v -> e v
lams tele s = quantify lam s tele

pis :: Syntax e => Telescope (Annotation e) e v -> Scope Tele e v -> e v
pis tele s = quantify pi_ s tele

arrow :: Syntax e => Annotation e -> e v -> e v -> e v
arrow p a b = pi_ mempty p a $ Scope $ pure $ F b
