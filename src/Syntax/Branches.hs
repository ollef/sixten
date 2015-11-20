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
import qualified Data.Vector as Vector

import Syntax.Annotation
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches d expr a
  = ConBranches [(Constr, Telescope d expr a, Scope Tele expr a)]
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches d) where
  ConBranches cbrs   >>>= f = ConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs]
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (HasPlicitness d, HasRelevance d, Monad f, Pretty (f v), IsString v) => Pretty (Branches d f v) where
  prettyM (ConBranches cbrs) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVars ns tele <+>
        prettyM "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!) . unTele) s)
    | (c, tele, s) <- cbrs]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> prettyM "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    [prettyM "_" <+> prettyM "->" <+> prettyM def]

trimapBranches :: Bifunctor expr
              => (d -> d') -> (x -> x') -> (y -> y')
              -> Branches d (expr x) y
              -> Branches d' (expr x') y'
trimapBranches e f g (ConBranches cbrs) = ConBranches [(c, trimapTelescope e f g t, bimapScope f g s) | (c, t, s) <- cbrs]
trimapBranches _ f g (LitBranches lbrs d) = LitBranches [(c, bimap f g e) | (c, e) <- lbrs] (bimap f g d)

trifoldMapBranches :: (Bifoldable expr, Monoid m)
                  => (d -> m) -> (x -> m) -> (y -> m)
                  -> Branches d (expr x) y
                  -> m
trifoldMapBranches e f g (ConBranches cbrs) = fold [trifoldMapTelescope e f g t <> bifoldMapScope f g s | (_, t, s) <- cbrs]
trifoldMapBranches _ f g (LitBranches lbrs d) = fold [bifoldMap f g e | (_, e) <- lbrs] <> bifoldMap f g d

tritraverseBranches :: (Bitraversable expr, Applicative f)
                   => (d -> f d') -> (x -> f x') -> (y -> f y')
                   -> Branches d (expr x) y
                   -> f (Branches d' (expr x') y')
tritraverseBranches e f g (ConBranches cbrs) =
  ConBranches <$> sequenceA [(,,) c <$> tritraverseTelescope e f g t <*> bitraverseScope f g s | (c, t, s) <- cbrs]
tritraverseBranches _ f g (LitBranches lbrs d) =
  LitBranches <$> sequenceA [(,) l <$> bitraverse f g e | (l, e) <- lbrs] <*> bitraverse f g d

exposeBranches :: Applicative expr
               => (forall v. expr v -> expr (Var e v))
               -> Branches d expr x
               -> Branches d expr (Var e x)
exposeBranches f (ConBranches cbrs) =
  ConBranches [(c, exposeTelescope f t, exposeScope f s) | (c, t, s) <- cbrs]
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)
