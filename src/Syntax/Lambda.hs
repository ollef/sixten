{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, Rank2Types, ViewPatterns #-}
module Syntax.Lambda where

import qualified Bound.Scope.Simple as Simple
import Data.Bifunctor
import Data.Monoid
import qualified Data.Set as S
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax
import Util

data Sized e v = Sized (e v) (e v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

type SExpr = Sized Expr

data Expr v
  = Var v
  | Global Name
  | Con QConstr (Vector (SExpr v)) -- ^ Fully applied
  | Lit Literal
  | Lam !NameHint (Expr v) (Simple.Scope () SExpr v)
  | App (SExpr v) (SExpr v)
  | Case (SExpr v) (SimpleBranches QConstr Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

appsView :: Expr v -> (Expr v, Vector (SExpr v))
appsView = go []
  where
    go args (App (Sized _ e1) se2) = go (se2:args) e1
    go args e = (e, Vector.reverse $ Vector.fromList args)

lamView :: SExpr v -> Maybe (NameHint, Expr v, Simple.Scope () SExpr v)
lamView (Sized _ (Lam h e s)) = Just (h, e, s)
lamView _ = Nothing

-------------------------------------------------------------------------------
-- Instances
instance Bound Sized where
  Sized s e >>>= f = Sized (s >>= f) (e >>= f)

instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr
instance Eq1 (Sized Expr)
instance Ord1 (Sized Expr)
instance Show1 (Sized Expr)

etaLam :: Hint (Maybe Name) -> Expr v -> Simple.Scope () SExpr v -> Expr v
etaLam _ _ (Simple.Scope (Sized _ (App (Sized _ e) (Sized _ (Var (B ()))))))
  | B () `S.notMember` toSet (second (const ()) <$> e)
    = unvar (error "etaLam") id <$> e
etaLam n e s = Lam n e s

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lit l -> prettyM l
    Lam h sz s -> withNameHint h $ \n ->
      prettyM "\\(" <> prettyM n <+> prettyM ":" <+> prettyM sz <> prettyM ")." <+>
        prettyM (instantiateVar (\() -> fromText n) s)
  {-
    (bindingsViewM lamView -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        prettyM "\\" <> prettyTeleVarTypes ns tele <> prettyM "." <+>
        associate absPrec (prettyM $ instantiateTeleVars (fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
    -}
    App e1 e2 -> parens `above` annoPrec $
      prettyApp (prettyM e1) (prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+>
      prettyM "of" <$$> indent 2 (prettyM brs)

instance Pretty (e v) => Pretty (Sized e v) where
  prettyM (Sized sz e) = parens `above` annoPrec $
    prettyM e <+> prettyM ":" <+> prettyM sz
