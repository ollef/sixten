{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types #-}
module Syntax.Branches where
import qualified Bound.Scope.Simple as Simple
import Bound
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c expr a
  = ConBranches [(c, Telescope expr a, Scope Tele expr a)] (expr a) -- ^ Return type
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches c) where
  ConBranches cbrs typ >>>= f = ConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs] (typ >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v)
  => Pretty (Branches c f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVarTypes ns tele <+>
        prettyM "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!) . unTele) s)
    | (c, tele, s) <- cbrs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> prettyM "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    [prettyM "_" <+> prettyM "->" <+> prettyM def]

exposeBranches :: Applicative expr
               => (forall v. expr v -> expr (Var e v))
               -> Branches c expr x
               -> Branches c expr (Var e x)
exposeBranches f (ConBranches cbrs typ) =
  ConBranches [(c, exposeTelescope f tele, exposeScope f s) | (c, tele, s) <- cbrs] (f typ)
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)

data SimpleBranches c expr a
  = SimpleConBranches [(c, SimpleTelescope expr a, Simple.Scope Tele expr a)]
  | SimpleLitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (SimpleBranches c) where
  SimpleConBranches cbrs >>>= f = SimpleConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs]
  SimpleLitBranches lbrs d >>>= f = SimpleLitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Eq v, Eq1 f, Functor f, Pretty c, Pretty (f v), IsString v)
  => Pretty (SimpleBranches c f v) where
  prettyM (SimpleConBranches cbrs) = vcat
    [ withSimpleTeleHints tele $ \ns ->
        prettyM c <+> prettySimpleTeleVarTypes ns tele <+>
        prettyM "->" <+> prettyM (instantiateVar (fromText . (ns Vector.!) . unTele) s)
    | (c, tele, s) <- cbrs ]
  prettyM (SimpleLitBranches lbrs def) = vcat $
    [ prettyM l <+> prettyM "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    [prettyM "_" <+> prettyM "->" <+> prettyM def]
