{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, OverloadedStrings #-}
module Syntax.Branches where
import qualified Bound.Scope.Simple as Simple
import Bound
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Annotation
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c expr v
  = ConBranches [(c, Telescope Scope Annotation expr v, Scope Tele expr v)] (expr v) -- ^ Return type
  | LitBranches [(Literal, expr v)] (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches c) where
  ConBranches cbrs typ >>>= f = ConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs] (typ >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Eq v, Eq1 f, Monad f, Pretty c, Pretty (f v), IsString v)
  => Pretty (Branches c f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVarTypes ns tele <+>
        "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!) . unTele) s)
    | (c, tele, s) <- cbrs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    ["_" <+> "->" <+> prettyM def]

exposeBranches :: Applicative expr
               => (forall v. expr v -> expr (Var e v))
               -> Branches c expr x
               -> Branches c expr (Var e x)
exposeBranches f (ConBranches cbrs typ) =
  ConBranches [(c, exposeTelescope f tele, exposeScope f s) | (c, tele, s) <- cbrs] (f typ)
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)

data SimpleBranches c expr v
  = SimpleConBranches [(c, Telescope Simple.Scope () expr v, Simple.Scope Tele expr v)]
  | SimpleLitBranches [(Literal, expr v)] (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (SimpleBranches c) where
  SimpleConBranches cbrs >>>= f = SimpleConBranches [(c, t >>>= f, s >>>= f) | (c, t, s) <- cbrs]
  SimpleLitBranches lbrs d >>>= f = SimpleLitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Eq v, Eq1 f, Functor f, Pretty c, Pretty (f v), IsString v)
  => Pretty (SimpleBranches c f v) where
  prettyM (SimpleConBranches cbrs) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettySimpleTeleVarTypes ns tele <+>
        "->" <+> prettyM (instantiateVar (fromText . (ns Vector.!) . unTele) s)
    | (c, tele, s) <- cbrs ]
  prettyM (SimpleLitBranches lbrs def) = vcat $
    [ prettyM l <+> "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    ["_" <+> "->" <+> prettyM def]
