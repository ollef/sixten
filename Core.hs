{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Core where

import Bound
import Bound.Scope
import Bound.Var
import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Monoid
import qualified Data.Set as S
import Data.String
import Data.Traversable
import Prelude.Extras

import Branches
import Pretty
import Util

data Expr v
  = Var v
  | Type -- Int
  | Pi  !(Hint (Maybe Name)) !Plicitness (Expr v) (Scope1 Expr v)
  | Lam !(Hint (Maybe Name)) !Plicitness (Expr v) (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr; instance Ord1 Expr; instance Show1 Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v       -> f v
    Type        -> Type
    Pi  x p t s -> Pi x p (t >>= f) (s >>>= f)
    Lam x p t s -> Lam x p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)

instance (IsString v, Pretty v) => Pretty (Expr v) where
  prettyPrec expr = case expr of
    Var v     -> prettyPrec v
    Type      -> pure $ text "Type"
    Pi  h p t s | null $ bindings s -> parens `above` arrPrec $ do
      a <- bracesWhen (p == Implicit) $ prettyPrec t
      b <- associate $ prettyPrec $ instantiate1 undefined s
      return $ a <+> text "->" <+> b

                | otherwise         -> withHint h $ \x -> parens `above` absPrec $ do
      vt <- inviolable $ bracesWhen (p == Implicit) $ ((text x <+> text ":") <+>) <$> prettyPrec t
      b <- associate  $ prettyPrec $ instantiate1 (return $ fromString x) s
      return $ text "forall" <+> vt <> text "." <+> b
    Lam h p t s -> withHint h $ \x -> parens `above` absPrec $ do
      vt <- inviolable $ bracesWhen (p == Implicit) $ ((text x <+> text ":") <+>) <$> prettyPrec t
      b <- associate  $ prettyPrec $ instantiate1 (return $ fromString x) s
      return $ text "\\" <> vt <> text "." <+> b
    App e1 p e2 -> prettyApp (prettyPrec e1) (bracesWhen (p == Implicit) $ prettyPrec e2)
    Case _ _ -> undefined

etaLam :: Ord v => Hint (Maybe Name) -> Plicitness -> Expr v -> Scope1 Expr v -> Expr v
etaLam _ p _ (Scope (Core.App e p' (Var (B ()))))
  | B () `S.notMember` foldMap S.singleton e && p == p'
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n p t s = Core.Lam n p t s
