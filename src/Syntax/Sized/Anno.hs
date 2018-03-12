{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Sized.Anno where

import Bound
import Bound.Scope
import Data.Deriving
import Data.Functor.Classes
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Util

data Anno e v = Anno (e v) (e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

typeAnno :: Anno e v -> e v
typeAnno (Anno _ t) = t

data AnnoScope b e a = AnnoScope (Scope b e a) (Scope b e a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type AnnoScope1 = AnnoScope ()

toAnnoScope :: Monad e => Anno e (Var b a) -> AnnoScope b e a
toAnnoScope (Anno e t) = AnnoScope (toScope e) (toScope t)

fromAnnoScope :: Monad e => AnnoScope b e a -> Anno e (Var b a)
fromAnnoScope (AnnoScope se st) = Anno (fromScope se) (fromScope st)

instantiateAnno :: Monad e => (b -> e a) -> AnnoScope b e a -> Anno e a
instantiateAnno f (AnnoScope se st) = Anno (instantiate f se) (instantiate f st)

instantiate1Anno :: Monad e => e a -> AnnoScope1 e a -> Anno e a
instantiate1Anno x (AnnoScope se st) = Anno (Util.instantiate1 x se) (Util.instantiate1 x st)

abstractAnno :: Monad e => (a -> Maybe b) -> Anno e a -> AnnoScope b e a
abstractAnno f (Anno e t) = AnnoScope (abstract f e) (abstract f t)

abstract1Anno :: (Monad e, Eq a) => a -> Anno e a -> AnnoScope1 e a
abstract1Anno a (Anno e t) = AnnoScope (abstract1 a e) (abstract1 a t)

instantiateAnnoLet
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> AnnoScope LetVar f a
  -> Anno f a
instantiateAnnoLet f vs
  = instantiateAnno (f . fromMaybe (error "instantiateAnnoLet") . (vs Vector.!?) . unLetVar)

mapAnnoBound :: Functor e => (b -> b') -> AnnoScope b e a -> AnnoScope b' e a
mapAnnoBound f (AnnoScope s s') = AnnoScope (mapBound f s) (mapBound f s')

annoBindingsViewM
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', AnnoScope1 expr' v'))
  -> expr' v
  -> Maybe (Telescope a expr v, AnnoScope TeleVar expr' v)
annoBindingsViewM f expr@(f -> Just _) = Just $ annoBindingsView f $ Anno expr $ error "annoBindingsViewM"
annoBindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
annoBindingsView
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', AnnoScope1 expr' v'))
  -> Anno expr' v
  -> (Telescope a expr v, AnnoScope TeleVar expr' v)
annoBindingsView f expr = go 0 $ F <$> expr
  where
    go x (Anno (f -> Just (n, p, e, s)) _) = (Telescope $ pure (TeleArg n p $ toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ instantiate1Anno (return $ B x) s
    go _ e = (Telescope mempty, toAnnoScope e)

instantiateAnnoTele
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> AnnoScope TeleVar f a
  -> Anno f a
instantiateAnnoTele f vs
  = instantiateAnno (f . fromMaybe (error "instantiateAnnoTele") . (vs Vector.!?) . unTeleVar)

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Anno
deriveOrd1 ''Anno
deriveShow1 ''Anno

instance MFunctor Anno where
  hoist f (Anno e t) = Anno (f e) (f t)

instance MFunctor (AnnoScope b) where
  hoist f (AnnoScope s t) = AnnoScope (hoist f s) (hoist f t)

instance GlobalBound Anno where
  bound f g (Anno e t) = Anno (bind f g e) (bind f g t)

instance GlobalBound (AnnoScope b) where
  bound f g (AnnoScope e t) = AnnoScope (bound f g e) (bound f g t)

instance (Eq b, Eq1 expr, Monad expr) => Eq1 (AnnoScope b expr) where
  liftEq = $(makeLiftEq ''AnnoScope)

instance (Ord b, Ord1 expr, Monad expr) => Ord1 (AnnoScope b expr) where
  liftCompare = $(makeLiftCompare ''AnnoScope)

instance (Show b, Show1 expr, Monad expr) => Show1 (AnnoScope b expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''AnnoScope)

instance Pretty (e v) => Pretty (Anno e v) where
  prettyM (Anno e t) = parens `above` annoPrec $
    prettyM e <+> ":" <+> prettyM t
