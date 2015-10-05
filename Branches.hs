{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Branches where
import Bound
import Data.Bifoldable
import Data.Bifunctor
import Data.Foldable
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Hint
import Util
import Pretty

data Branches expr a
  = ConBranches [(Constr, Vector NameHint, Scope Int expr a)]
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound Branches where
  ConBranches cbrs   >>>= f = ConBranches [(c, ns, s >>>= f) | (c, ns, s) <- cbrs]
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>=  f) | (l, e) <- lbrs] (d >>= f)

instance (Monad f, Pretty (f v), IsString v) => Pretty (Branches f v) where
  prettyM (ConBranches cbrs) = vcat
    [ withNameHints vs $ \ns ->
        prettyM c <+> hsep (map prettyM $ Vector.toList ns) <+>
        prettyM "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!)) s)
    | (c, vs, s) <- cbrs]
  prettyM (LitBranches lbrs def) = vcat
    [ l <+> prettyM "->" <+> prettyM e
    | (l, e) <- map (first prettyM) lbrs ++ [(prettyM "_", def)]]

bimapBranches :: Bifunctor expr
              => (x -> x') -> (y -> y')
              -> Branches (expr x) y
              -> Branches (expr x') y'
bimapBranches f g (ConBranches cbrs) = ConBranches [(c, ns, bimapScope f g s) | (c, ns, s) <- cbrs]
bimapBranches f g (LitBranches lbrs d) = LitBranches [(c, bimap f g e) | (c, e) <- lbrs] (bimap f g d)

bifoldMapBranches :: (Bifoldable expr, Monoid m)
                  => (x -> m) -> (y -> m)
                  -> Branches (expr x) y
                  -> m
bifoldMapBranches f g (ConBranches cbrs) = fold [bifoldMapScope f g s | (_, _, s) <- cbrs]
bifoldMapBranches f g (LitBranches lbrs d) = fold [bifoldMap f g e | (_, e) <- lbrs] <> bifoldMap f g d
