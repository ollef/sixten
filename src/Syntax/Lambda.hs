{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Syntax.Lambda where

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import qualified Data.Set as S
import Data.String
import Data.Vector(Vector)
import Prelude.Extras

import Syntax
import Util

data Expr v
  = Var v
  | Global Name
  | Con QConstr (Vector (Expr v, Expr v)) -- ^ Fully applied
  | Lit Literal
  | Lam !NameHint (Expr v) (Scope1 Expr v)
  | App (Expr v) (Expr v)
  | Case (Expr v) (Branches QConstr Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

globals :: Expr v -> Expr (Var Name v)
globals expr = case expr of
  Var v -> Var $ F v
  Global g -> Var $ B g
  Lit l -> Lit l
  Con c es -> Con c $ bimap globals globals <$> es
  Lam h e s -> Lam h (globals e) $ exposeScope globals s
  App e1 e2 -> App (globals e1) (globals e2)
  Case e brs -> Case (globals e) (exposeBranches globals brs)

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance Syntax Expr where
  pi_ _ _ _ _ = Lit 0
  piView _ = Nothing

  lam h _ = Lam h

  lamView (Lam n e s) = Just (n, ReEx, e, s)
  lamView _ = Nothing

  app e1 _ = App e1

  appView (App e1 e2) = Just (e1, ReEx, e2)
  appView _ = Nothing


instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  Var v >>= f = f v
  Global g >>= _ = Global g
  Con c es >>= f = Con c $ (\(e, sz) -> (e >>= f, sz >>= f)) <$> es
  Lit l >>= _ = Lit l
  Lam h e s >>= f = Lam h (e >>= f) $ s >>>= f
  App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)
  Case e brs >>= f = Case (e >>= f) (brs >>>= f)

etaLam :: Hint (Maybe Name) -> Expr v -> Scope1 Expr v -> Expr v
etaLam _ _ (Scope (App e (Var (B ()))))
  | B () `S.notMember` toSet (second (const ()) <$> e)
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n e s = Lam n e s

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c es -> prettyApps (prettyM c)
              $ (\(e, sz) -> parens `above` annoPrec $ prettyM e <+> prettyM ":" <+> prettyM sz) <$> es
    Lit l -> prettyM l
    (bindingsViewM lamView -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        prettyM "\\" <> prettyTeleVarTypes ns tele <> prettyM "." <+>
        associate absPrec (prettyM $ instantiateTele (pure . fromText <$> ns) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 e2 -> prettyApp (prettyM e1) (prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+> prettyM "of" <$$> indent 2 (prettyM brs)
