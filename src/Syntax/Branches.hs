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
import Util

data Branches expr a
  = ConBranches [(Constr, Vector (NameHint, Plicitness), Scope Int expr a)]
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound Branches where
  ConBranches cbrs   >>>= f = ConBranches [(c, ns, s >>>= f) | (c, ns, s) <- cbrs]
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>=  f) | (l, e) <- lbrs] (d >>= f)

instance (Monad f, Pretty (f v), IsString v) => Pretty (Branches f v) where
  prettyM (ConBranches cbrs) = vcat
    [ withNameHints (fst <$> vs) $ \ns ->
        prettyM c <+> hsep (map (\(p, x) -> braces `iff` isImplicit p $ prettyM x)
                                $ Vector.toList $ Vector.zip (snd <$> vs) ns) <+>
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

bitraverseBranches :: (Bitraversable expr, Applicative f)
                   => (x -> f x') -> (y -> f y')
                   -> Branches (expr x) y
                   -> f (Branches (expr x') y')
bitraverseBranches f g (ConBranches cbrs) =
  ConBranches <$> sequenceA [(,,) h p <$> bitraverseScope f g s | (h, p, s) <- cbrs]
bitraverseBranches f g (LitBranches lbrs d) =
  LitBranches <$> sequenceA [(,) l <$> bitraverse f g e | (l, e) <- lbrs] <*> bitraverse f g d

exposeBranches :: Applicative expr
               => (forall x. expr x -> expr (Var e x))
               -> Branches expr a
               -> Branches expr (Var e a)
exposeBranches f (ConBranches cbrs) =
  ConBranches [(c, hs, exposeScope f s) | (c, hs, s) <- cbrs]
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)
