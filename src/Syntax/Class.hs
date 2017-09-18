{-# LANGUAGE ViewPatterns #-}
module Syntax.Class where
import Bound
import Data.Bifunctor
import Data.Foldable as Foldable

import Syntax.Annotation
import Syntax.Hint
import Syntax.Telescope
import Util
import Util.Tsil

class (AppSyntax e, Monad e, Traversable e) => Syntax e where
  lam :: NameHint -> Plicitness -> e v -> Scope1 e v -> e v
  lamView :: e v -> Maybe (NameHint, Plicitness, e v, Scope1 e v)

  pi_ :: NameHint -> Plicitness -> e v -> Scope1 e v -> e v
  piView :: e v -> Maybe (NameHint, Plicitness, e v, Scope1 e v)

class AppSyntax e where
  app :: e v -> Plicitness -> e v -> e v
  appView :: e v -> Maybe (e v, Plicitness, e v)

apps :: (AppSyntax e, Foldable t) => e v -> t (Plicitness, e v) -> e v
apps = Foldable.foldl' (uncurry . app)

appsView :: AppSyntax e => e v -> (e v, [(Plicitness, e v)])
appsView = second toList . go
  where
    go (appView -> Just (e1, p, e2)) = second (`Snoc` (p, e2)) $ go e1
    go e = (e, Nil)

typeApp :: Syntax e => e v -> e v -> Maybe (e v)
typeApp (piView -> Just (_, _, _, s)) e = Just $ Util.instantiate1 e s
typeApp _ _ = Nothing

typeApps :: (Syntax e, Foldable t) => e v -> t (e v) -> Maybe (e v)
typeApps = foldlM typeApp

usedPiView
  :: Syntax e
  => e v
  -> Maybe (NameHint, Plicitness, e v, Scope1 e v)
usedPiView (piView -> Just (n, p, e, s@(unusedScope -> Nothing))) = Just (n, p, e, s)
usedPiView _ = Nothing

usedPisViewM :: Syntax e => e v -> Maybe (Telescope Plicitness e v, Scope TeleVar e v)
usedPisViewM = bindingsViewM usedPiView

telescope :: Syntax e => e v -> Telescope Plicitness e v
telescope (pisView -> (tele, _)) = tele

pisView :: Syntax e => e v -> (Telescope Plicitness e v, Scope TeleVar e v)
pisView = bindingsView piView

pisViewM :: Syntax e => e v -> Maybe (Telescope Plicitness e v, Scope TeleVar e v)
pisViewM = bindingsViewM piView

lamsView :: Syntax e => e v -> (Telescope Plicitness e v, Scope TeleVar e v)
lamsView = bindingsView lamView

lamsViewM :: Syntax e => e v -> Maybe (Telescope Plicitness e v, Scope TeleVar e v)
lamsViewM = bindingsViewM lamView

lams :: Syntax e => Telescope Plicitness e v -> Scope TeleVar e v -> e v
lams tele s = quantify lam s tele

pis :: Syntax e => Telescope Plicitness e v -> Scope TeleVar e v -> e v
pis tele s = quantify pi_ s tele

arrow :: Syntax e => Plicitness -> e v -> e v -> e v
arrow p a b = pi_ mempty p a $ Scope $ pure $ F b
