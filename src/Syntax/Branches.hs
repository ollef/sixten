{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, MonadComprehensions, Rank2Types, OverloadedStrings #-}
module Syntax.Branches where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid as Monoid
import Data.Semigroup as Semigroup
import Data.String
import Prelude.Extras

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope
import Util

data Branches c a expr v
  = ConBranches [(c, Telescope a expr v, Scope Tele expr v)]
  | LitBranches (NonEmpty (Literal, expr v)) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance GlobalBound (Branches c a) where
  bound f g (ConBranches cbrs) = ConBranches
    [(c, bound f g a, bound f g s) | (c, a, s) <- cbrs]
  bound f g (LitBranches lbrs def) = LitBranches
    [(l, bind f g e) | (l, e) <- lbrs]
    (bind f g def)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v, Eq a, PrettyAnnotation a)
  => Pretty (Branches c a f v) where
  prettyM (ConBranches cbrs) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVarTypes ns tele <+>
        "->" <+> prettyM (instantiateTele (pure . fromName) ns s)
    | (c, tele, s) <- cbrs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> "->" <+> prettyM e
    | (l, e) <- lbrs] Semigroup.<>
    pure ("_" <+> "->" <+> prettyM def)

bimapAnnotatedBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c a (expr a) v
  -> Branches c a' (expr a') v'
bimapAnnotatedBranches f g (ConBranches cbrs)
  = ConBranches [(c, bimapAnnotatedTelescope f g tele, bimapScope f g s) | (c, tele, s) <- cbrs]
bimapAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches [(l, bimap f g br) | (l, br) <- lbrs] $ bimap f g def

bifoldMapAnnotatedBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c a (expr a) v
  -> m
bifoldMapAnnotatedBranches f g (ConBranches cbrs)
  = mconcat [bifoldMapAnnotatedTelescope f g tele Monoid.<> bifoldMapScope f g s | (_, tele, s) <- cbrs]
bifoldMapAnnotatedBranches f g (LitBranches lbrs def)
  = mconcat (NonEmpty.toList [bifoldMap f g br | (_, br) <- lbrs]) Monoid.<> bifoldMap f g def

bitraverseAnnotatedBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c a (expr a) v
  -> f (Branches c a' (expr a') v')
bitraverseAnnotatedBranches f g (ConBranches cbrs)
  = ConBranches
  <$> traverse
    (\(c, tele, br) -> (,,) c <$> bitraverseAnnotatedTelescope f g tele <*> bitraverseScope f g br)
    cbrs
bitraverseAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(l, br) -> (,) l <$> bitraverse f g br) lbrs <*> bitraverse f g def

bimapBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c p (expr a) v
  -> Branches c p (expr a') v'
bimapBranches f g (ConBranches cbrs)
  = ConBranches [(c, bimapTelescope f g tele, bimapScope f g s) | (c, tele, s) <- cbrs]
bimapBranches f g (LitBranches lbrs def)
  = LitBranches [(l, bimap f g br) | (l, br) <- lbrs] $ bimap f g def

bifoldMapBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c p (expr a) v
  -> m
bifoldMapBranches f g (ConBranches cbrs)
  = mconcat [bifoldMapTelescope f g tele Monoid.<> bifoldMapScope f g s | (_, tele, s) <- cbrs]
bifoldMapBranches f g (LitBranches lbrs def)
  = mconcat (NonEmpty.toList [bifoldMap f g br | (_, br) <- lbrs]) Monoid.<> bifoldMap f g def

bitraverseBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c p (expr a) v
  -> f (Branches c p (expr a') v')
bitraverseBranches f g (ConBranches cbrs)
  = ConBranches
  <$> traverse
    (\(c, tele, br) -> (,,) c <$> bitraverseTelescope f g tele <*> bitraverseScope f g br)
    cbrs
bitraverseBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(l, br) -> (,) l <$> bitraverse f g br) lbrs <*> bitraverse f g def

instance MFunctor (Branches c p) where
  hoist f (ConBranches cbrs)
    = ConBranches [(c, hoist f tele, hoist f s) | (c, tele, s) <- cbrs]
  hoist f (LitBranches lbrs def)
    = LitBranches [(l, f e) | (l, e) <- lbrs] $ f def
