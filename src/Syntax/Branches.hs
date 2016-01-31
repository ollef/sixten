{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types #-}
module Syntax.Branches where
import Bound
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax.Plicitness
import Syntax.Hint
import Syntax.Pretty
import Syntax.Telescope
import Util

data Branches c expr a
  = ConBranches [(c, Vector (NameHint, Plicitness), Scope Tele expr a)] (expr a) -- ^ Return type
  | LitBranches [(Literal, expr a)] (expr a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound (Branches c) where
  ConBranches cbrs typ >>>= f = ConBranches [(c, t, s >>>= f) | (c, t, s) <- cbrs] (typ >>= f)
  LitBranches lbrs d >>>= f = LitBranches [(l, e >>= f) | (l, e) <- lbrs] (d >>= f)

instance (Monad f, Pretty c, Pretty (f v), IsString v)
  => Pretty (Branches c f v) where
  prettyM (ConBranches cbrs _) = vcat
    [ withTeleHints tele $ \ns ->
        prettyM c <+> prettyTeleVars ns tele <+>
        prettyM "->" <+> prettyM (instantiate (pure . fromText . (ns Vector.!) . unTele) s)
    | (c, xs, s) <- cbrs, let tele = Telescope $ (\(x, d) -> (x, d, undefined)) <$> xs ]
  prettyM (LitBranches lbrs def) = vcat $
    [ prettyM l <+> prettyM "->" <+> prettyM e
    | (l, e) <- lbrs] ++
    [prettyM "_" <+> prettyM "->" <+> prettyM def]

exposeBranches :: Applicative expr
               => (forall v. expr v -> expr (Var e v))
               -> Branches c expr x
               -> Branches c expr (Var e x)
exposeBranches f (ConBranches cbrs typ) =
  ConBranches [(c, t, exposeScope f s) | (c, t, s) <- cbrs] (f typ)
exposeBranches f (LitBranches lbrs def) =
  LitBranches [(l, f e) | (l, e) <- lbrs] (f def)
