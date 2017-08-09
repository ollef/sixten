{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, MonadComprehensions, Rank2Types, OverloadedStrings, TemplateHaskell #-}
module Syntax.Branches where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Deriving
import Data.Functor.Classes
import Data.List.NonEmpty(NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid as Monoid
import Data.Semigroup as Semigroup
import Data.String

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Literal
import Syntax.Name
import Syntax.Telescope
import Util

data Branches c a expr v
  = ConBranches [ConBranch c a expr v]
  | LitBranches (NonEmpty (LitBranch expr v)) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ConBranch c a expr v = ConBranch c (Telescope a expr v) (Scope Tele expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
data LitBranch expr v = LitBranch Literal (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

bimapAnnotatedBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c a (expr a) v
  -> Branches c a' (expr a') v'
bimapAnnotatedBranches f g (ConBranches cbrs)
  = ConBranches [ConBranch c (bimapAnnotatedTelescope f g tele) (bimapScope f g s) | ConBranch c tele s <- cbrs]
bimapAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches [LitBranch l (bimap f g br) | LitBranch l br <- lbrs] $ bimap f g def

bifoldMapAnnotatedBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c a (expr a) v
  -> m
bifoldMapAnnotatedBranches f g (ConBranches cbrs)
  = mconcat [bifoldMapAnnotatedTelescope f g tele Monoid.<> bifoldMapScope f g s | ConBranch _ tele s <- cbrs]
bifoldMapAnnotatedBranches f g (LitBranches lbrs def)
  = mconcat (NonEmpty.toList [bifoldMap f g br | LitBranch _ br <- lbrs]) Monoid.<> bifoldMap f g def

bitraverseAnnotatedBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c a (expr a) v
  -> f (Branches c a' (expr a') v')
bitraverseAnnotatedBranches f g (ConBranches cbrs)
  = ConBranches
  <$> traverse
    (\(ConBranch c tele br) -> ConBranch c <$> bitraverseAnnotatedTelescope f g tele <*> bitraverseScope f g br)
    cbrs
bitraverseAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(LitBranch l br) -> LitBranch l <$> bitraverse f g br) lbrs <*> bitraverse f g def

bimapBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c p (expr a) v
  -> Branches c p (expr a') v'
bimapBranches f g (ConBranches cbrs)
  = ConBranches [ConBranch c (bimapTelescope f g tele) (bimapScope f g s) | ConBranch c tele s <- cbrs]
bimapBranches f g (LitBranches lbrs def)
  = LitBranches [LitBranch l (bimap f g br) | LitBranch l br <- lbrs] $ bimap f g def

bifoldMapBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c p (expr a) v
  -> m
bifoldMapBranches f g (ConBranches cbrs)
  = mconcat [bifoldMapTelescope f g tele Monoid.<> bifoldMapScope f g s | ConBranch _ tele s <- cbrs]
bifoldMapBranches f g (LitBranches lbrs def)
  = mconcat (NonEmpty.toList [bifoldMap f g br | LitBranch _ br <- lbrs]) Monoid.<> bifoldMap f g def

bitraverseBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c p (expr a) v
  -> f (Branches c p (expr a') v')
bitraverseBranches f g (ConBranches cbrs)
  = ConBranches
  <$> traverse
    (\(ConBranch c tele br) -> ConBranch c <$> bitraverseTelescope f g tele <*> bitraverseScope f g br)
    cbrs
bitraverseBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(LitBranch l br) -> LitBranch l <$> bitraverse f g br) lbrs <*> bitraverse f g def

-------------------------------------------------------------------------------
-- Instances
instance MFunctor (Branches c p) where
  hoist f (ConBranches cbrs)
    = ConBranches [ConBranch c (hoist f tele) (hoist f s) | ConBranch c tele s <- cbrs]
  hoist f (LitBranches lbrs def)
    = LitBranches [LitBranch l (f e) | LitBranch l e <- lbrs] $ f def

instance GlobalBound (Branches c a) where
  bound f g (ConBranches cbrs) = ConBranches $ bound f g <$> cbrs
  bound f g (LitBranches lbrs def) = LitBranches
    (bound f g <$> lbrs)
    (bind f g def)

instance GlobalBound (ConBranch c a) where
  bound f g (ConBranch c a s) = ConBranch c (bound f g a) (bound f g s)
instance GlobalBound LitBranch where
  bound f g (LitBranch l s) = LitBranch l (bind f g s)

$(return mempty)

instance (Eq c, Eq a, Eq1 expr, Monad expr) => Eq1 (Branches c a expr) where
  liftEq = $(makeLiftEq ''Branches)
instance (Ord c, Ord a, Ord1 expr, Monad expr) => Ord1 (Branches c a expr) where
  liftCompare = $(makeLiftCompare ''Branches)
instance (Show c, Show a, Show1 expr, Monad expr) => Show1 (Branches c a expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Branches)

instance (Eq c, Eq a, Eq1 expr, Monad expr) => Eq1 (ConBranch c a expr) where
  liftEq = $(makeLiftEq ''ConBranch)
instance (Ord c, Ord a, Ord1 expr, Monad expr) => Ord1 (ConBranch c a expr) where
  liftCompare = $(makeLiftCompare ''ConBranch)
instance (Show c, Show a, Show1 expr, Monad expr) => Show1 (ConBranch c a expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''ConBranch)

instance Eq1 expr => Eq1 (LitBranch expr) where
  liftEq = $(makeLiftEq ''LitBranch)
instance Ord1 expr => Ord1 (LitBranch expr) where
  liftCompare = $(makeLiftCompare ''LitBranch)
instance Show1 expr => Show1 (LitBranch expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LitBranch)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v, Eq a, PrettyAnnotation a)
  => Pretty (Branches c a f v) where
  prettyM (ConBranches cbrs) = vcat $ prettyM <$> cbrs
  prettyM (LitBranches lbrs def) = vcat $
    (prettyM <$> lbrs) Semigroup.<>
    pure ("_" <+> "->" <+> prettyM def)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v, PrettyAnnotation a)
  => Pretty (ConBranch c a f v) where
  prettyM (ConBranch c tele s) = withTeleHints tele $ \ns ->
    prettyM c <+> prettyTeleVarTypes ns tele <+>
      "->" <+> prettyM (instantiateTele (pure . fromName) ns s)
instance Pretty (f v) => Pretty (LitBranch f v) where
  prettyM (LitBranch l e) = prettyM l <+> "->" <+> prettyM e
