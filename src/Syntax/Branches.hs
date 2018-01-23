{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, MonadComprehensions, Rank2Types, OverloadedStrings, TemplateHaskell #-}
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

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Literal
import Syntax.Module
import Syntax.Name
import Syntax.Telescope
import Util

data Branches a expr v
  = ConBranches [ConBranch a expr v]
  | LitBranches (NonEmpty (LitBranch expr v)) (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data ConBranch a expr v = ConBranch QConstr (Telescope a expr v) (Scope TeleVar expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)
data LitBranch expr v = LitBranch Literal (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

bimapBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches p (expr a) v
  -> Branches p (expr a') v'
bimapBranches f g (ConBranches cbrs)
  = ConBranches [ConBranch c (bimapTelescope f g tele) (bimapScope f g s) | ConBranch c tele s <- cbrs]
bimapBranches f g (LitBranches lbrs def)
  = LitBranches [LitBranch l (bimap f g br) | LitBranch l br <- lbrs] $ bimap f g def

bifoldMapBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches p (expr a) v
  -> m
bifoldMapBranches f g (ConBranches cbrs)
  = mconcat [bifoldMapTelescope f g tele Monoid.<> bifoldMapScope f g s | ConBranch _ tele s <- cbrs]
bifoldMapBranches f g (LitBranches lbrs def)
  = mconcat (NonEmpty.toList [bifoldMap f g br | LitBranch _ br <- lbrs]) Monoid.<> bifoldMap f g def

bitraverseBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches p (expr a) v
  -> f (Branches p (expr a') v')
bitraverseBranches f g (ConBranches cbrs)
  = ConBranches
  <$> traverse
    (\(ConBranch c tele br) -> ConBranch c <$> bitraverseTelescope f g tele <*> bitraverseScope f g br)
    cbrs
bitraverseBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(LitBranch l br) -> LitBranch l <$> bitraverse f g br) lbrs <*> bitraverse f g def

-------------------------------------------------------------------------------
-- Instances
instance MFunctor (Branches p) where
  hoist f (ConBranches cbrs)
    = ConBranches [ConBranch c (hoist f tele) (hoist f s) | ConBranch c tele s <- cbrs]
  hoist f (LitBranches lbrs def)
    = LitBranches [LitBranch l (f e) | LitBranch l e <- lbrs] $ f def

instance GlobalBound (Branches a) where
  bound f g (ConBranches cbrs) = ConBranches $ bound f g <$> cbrs
  bound f g (LitBranches lbrs def) = LitBranches
    (bound f g <$> lbrs)
    (bind f g def)

instance GlobalBound (ConBranch a) where
  bound f g (ConBranch c a s) = ConBranch c (bound f g a) (bound f g s)
instance GlobalBound LitBranch where
  bound f g (LitBranch l s) = LitBranch l (bind f g s)

$(return mempty)

instance (Eq a, Eq1 expr, Monad expr) => Eq1 (Branches a expr) where
  liftEq = $(makeLiftEq ''Branches)
instance (Ord a, Ord1 expr, Monad expr) => Ord1 (Branches a expr) where
  liftCompare = $(makeLiftCompare ''Branches)
instance (Show a, Show1 expr, Monad expr) => Show1 (Branches a expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Branches)

instance (Eq a, Eq1 expr, Monad expr) => Eq1 (ConBranch a expr) where
  liftEq = $(makeLiftEq ''ConBranch)
instance (Ord a, Ord1 expr, Monad expr) => Ord1 (ConBranch a expr) where
  liftCompare = $(makeLiftCompare ''ConBranch)
instance (Show a, Show1 expr, Monad expr) => Show1 (ConBranch a expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''ConBranch)

instance Eq1 expr => Eq1 (LitBranch expr) where
  liftEq = $(makeLiftEq ''LitBranch)
instance Ord1 expr => Ord1 (LitBranch expr) where
  liftCompare = $(makeLiftCompare ''LitBranch)
instance Show1 expr => Show1 (LitBranch expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LitBranch)

instance (v ~ Doc, Eq1 f, Monad f, Pretty (f Doc), Eq a, PrettyAnnotation a)
  => Pretty (Branches a f v) where
  prettyM (ConBranches cbrs) = vcat $ prettyM <$> cbrs
  prettyM (LitBranches lbrs def) = vcat $
    (prettyM <$> lbrs) Semigroup.<>
    pure ("_" <+> "->" <+> prettyM def)

instance (v ~ Doc, Eq1 f, Monad f, Pretty (f Doc), PrettyAnnotation a)
  => Pretty (ConBranch a f v) where
  prettyM (ConBranch c tele s) = withTeleHints tele $ \ns ->
    prettyM c <+> prettyTeleVarTypes ns tele <+>
      "->" <+> prettyM (instantiateTele (pure . fromName) ns s)
instance Pretty (f v) => Pretty (LitBranch f v) where
  prettyM (LitBranch l e) = prettyM l <+> "->" <+> prettyM e
