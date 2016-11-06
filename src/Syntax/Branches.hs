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
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c a expr v
  = ConBranches [(c, Telescope a expr v, Scope Tele expr v)] (expr v) -- ^ Return type
  | LitBranches [(Literal, expr v)] (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

bindBranchesGlobals
  :: Monad e
  => (forall x. (n -> e x) -> e x -> e x)
  -> (n -> e v)
  -> Branches c a e v
  -> Branches c a e v
bindBranchesGlobals expr f (ConBranches cbrs typ) = ConBranches
  [(c, a, bindScopeGlobals expr f s) | (c, a, s) <- cbrs]
  (expr f typ)
bindBranchesGlobals expr f (LitBranches lbrs def) = LitBranches
  [(l, expr f e) | (l, e) <- lbrs]
  (expr f def)

instance Bound (Branches c a) where
  ConBranches cbrs typ >>>= f = ConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs] (typ >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v, Eq a, PrettyAnnotation a)
  => Pretty (Branches c a f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVarTypes ns tele <+>
        "->" <+> prettyM (instantiateTele (pure . fromText <$> ns) s)
    | (c, tele, s) <- cbrs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    ["_" <+> "->" <+> prettyM def]

bimapBranches
  :: Bifunctor expr
  => (a -> a')
  -> (v -> v')
  -> Branches c a (expr a) v
  -> Branches c a' (expr a') v'
bimapBranches f g (ConBranches cbrs typ)
  = ConBranches [(c, bimapTelescope f g tele, bimapScope f g s) | (c, tele, s) <- cbrs]
  $ bimap f g typ
bimapBranches f g (LitBranches lbrs def)
  = LitBranches [(l, bimap f g br) | (l, br) <- lbrs] $ bimap f g def

bifoldMapBranches
  :: (Bifoldable expr, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Branches c a (expr a) v
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
  -> Branches c a (expr a) v
  -> f (Branches c a' (expr a') v')
bitraverseBranches f g (ConBranches cbrs typ)
  = ConBranches
  <$> traverse
    (\(c, tele, br) -> (,,) c <$> bitraverseTelescope f g tele <*> bitraverseScope f g br)
    cbrs
  <*> bitraverse f g typ
bitraverseBranches f g (LitBranches lbrs def)
  = LitBranches <$> traverse (\(l, br) -> (,) l <$> bitraverse f g br) lbrs <*> bitraverse f g def
