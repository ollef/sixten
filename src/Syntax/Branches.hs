{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, OverloadedStrings #-}
module Syntax.Branches where
import Bound
import Bound.Scope
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import Data.String
import Prelude.Extras

import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c a expr v
  = ConBranches [(c, Telescope a expr v, Scope Tele expr v)] (expr v) -- ^ Return type
  | LitBranches [(Literal, expr v)] (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches c a) where
  ConBranches cbrs typ >>>= f = ConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs] (typ >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance GlobalBound (Branches c a) where
  bound f g (ConBranches cbrs typ) = ConBranches
    [(c, bound f g a, bound f g s) | (c, a, s) <- cbrs]
    (bind f g typ)
  bound f g (LitBranches lbrs def) = LitBranches
    [(l, bind f g e) | (l, e) <- lbrs]
    (bind f g def)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v, Eq a, PrettyAnnotation a)
  => Pretty (Branches c a f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVarTypes ns tele <+>
        "->" <+> prettyM (instantiateTele (pure . fromName <$> ns) s)
    | (c, tele, s) <- cbrs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    ["_" <+> "->" <+> prettyM def]

bimapAnnotatedBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c a (expr a) v
  -> Branches c a' (expr a') v'
bimapAnnotatedBranches f g (ConBranches cbrs typ)
  = ConBranches [(c, bimapAnnotatedTelescope f g tele, bimapScope f g s) | (c, tele, s) <- cbrs]
  $ bimap f g typ
bimapAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches [(l, bimap f g br) | (l, br) <- lbrs] $ bimap f g def

bifoldMapAnnotatedBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c a (expr a) v
  -> m
bifoldMapAnnotatedBranches f g (ConBranches cbrs typ)
  = mconcat [bifoldMapAnnotatedTelescope f g tele <> bifoldMapScope f g s | (_, tele, s) <- cbrs]
  <> bifoldMap f g typ
bifoldMapAnnotatedBranches f g (LitBranches lbrs def)
  = mconcat [bifoldMap f g br | (_, br) <- lbrs] <> bifoldMap f g def

bitraverseAnnotatedBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c a (expr a) v
  -> f (Branches c a' (expr a') v')
bitraverseAnnotatedBranches f g (ConBranches cbrs typ)
  = ConBranches
  <$> traverse
    (\(c, tele, br) -> (,,) c <$> bitraverseAnnotatedTelescope f g tele <*> bitraverseScope f g br)
    cbrs
  <*> bitraverse f g typ
bitraverseAnnotatedBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(l, br) -> (,) l <$> bitraverse f g br) lbrs <*> bitraverse f g def

bimapBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c p (expr a) v
  -> Branches c p (expr a') v'
bimapBranches f g (ConBranches cbrs typ)
  = ConBranches [(c, bimapTelescope f g tele, bimapScope f g s) | (c, tele, s) <- cbrs]
  $ bimap f g typ
bimapBranches f g (LitBranches lbrs def)
  = LitBranches [(l, bimap f g br) | (l, br) <- lbrs] $ bimap f g def

bifoldMapBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c p (expr a) v
  -> m
bifoldMapBranches f g (ConBranches cbrs typ)
  = mconcat [bifoldMapTelescope f g tele <> bifoldMapScope f g s | (_, tele, s) <- cbrs]
  <> bifoldMap f g typ
bifoldMapBranches f g (LitBranches lbrs def)
  = mconcat [bifoldMap f g br | (_, br) <- lbrs] <> bifoldMap f g def

bitraverseBranches
  :: (Bitraversable expr, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Branches c p (expr a) v
  -> f (Branches c p (expr a') v')
bitraverseBranches f g (ConBranches cbrs typ)
  = ConBranches
  <$> traverse
    (\(c, tele, br) -> (,,) c <$> bitraverseTelescope f g tele <*> bitraverseScope f g br)
    cbrs
  <*> bitraverse f g typ
bitraverseBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(l, br) -> (,) l <$> bitraverse f g br) lbrs <*> bitraverse f g def
