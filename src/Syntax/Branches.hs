{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types #-}
module Syntax.Branches where
import Bound
import Bound.Scope
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax.Annotation
import Syntax.Hint
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c d expr a
  -- TODO is the Telescope necessary here?
  = ConBranches [(c, Vector (NameHint, d), Scope Tele expr a)] (expr a) -- ^ Return type
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches c d) where
  ConBranches cbrs t >>>= f = ConBranches [(c, t, s >>>= f) | (c, t, s) <- cbrs] (t >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (HasPlicitness d, HasRelevance d, Monad f, Pretty c, Pretty (f v), IsString v) => Pretty (Branches c d f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVars ns tele <+>
        prettyM "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!) . unTele) s)
    | (c, xs, s) <- cbrs, let tele = Telescope $ (\(x, d) -> (x, d, undefined)) <$> xs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> prettyM "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    [prettyM "_" <+> prettyM "->" <+> prettyM def]

trimapBranches :: Bifunctor expr
              => (d -> d') -> (x -> x') -> (y -> y')
              -> Branches c d (expr x) y
              -> Branches c d' (expr x') y'
trimapBranches e f g (ConBranches cbrs typ) = ConBranches [(c, second e <$> t, bimapScope f g s) | (c, t, s) <- cbrs] (bimap f g typ)
trimapBranches _ f g (LitBranches lbrs d) = LitBranches [(c, bimap f g e) | (c, e) <- lbrs] (bimap f g d)

trifoldMapBranches :: (Bifoldable expr, Monoid m)
                  => (d -> m) -> (x -> m) -> (y -> m)
                  -> Branches c d (expr x) y
                  -> m
trifoldMapBranches e f g (ConBranches cbrs typ) = fold [foldMap (foldMap e) t <> bifoldMapScope f g s | (_, t, s) <- cbrs] <> bifoldMap f g typ
trifoldMapBranches _ f g (LitBranches lbrs d) = fold [bifoldMap f g e | (_, e) <- lbrs] <> bifoldMap f g d

tritraverseBranches :: (Bitraversable expr, Applicative f)
                   => (d -> f d') -> (x -> f x') -> (y -> f y')
                   -> Branches c d (expr x) y
                   -> f (Branches c d' (expr x') y')
tritraverseBranches e f g (ConBranches cbrs typ) =
  ConBranches <$> sequenceA [(,,) c <$> traverse (traverse e) t <*> bitraverseScope f g s | (c, t, s) <- cbrs] <*> bitraverse f g typ
tritraverseBranches _ f g (LitBranches lbrs d) =
  LitBranches <$> sequenceA [(,) l <$> bitraverse f g e | (l, e) <- lbrs] <*> bitraverse f g d

exposeBranches :: Applicative expr
               => (forall v. expr v -> expr (Var e v))
               -> Branches c d expr x
               -> Branches c d expr (Var e x)
exposeBranches f (ConBranches cbrs typ) =
  ConBranches [(c, t, exposeScope f s) | (c, t, s) <- cbrs] (f typ)
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)
