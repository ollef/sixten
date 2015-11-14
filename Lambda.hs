{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Lambda where
import Bound
import Bound.Var
import Control.Monad
import Data.Bifunctor
import Data.Monoid
import qualified Data.Set as S
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Branches
import Hint
import Pretty
import Util

data Expr v
  = Var v
  | Global Name
  | Con Constr
  | Lam !NameHint (Scope1 Expr v)
  | App (Expr v) (Expr v)
  | Case (Expr v) (Branches Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

globals :: Expr v -> Expr (Var Name v)
globals expr = case expr of
  Var v    -> Var $ F v
  Global g -> Var $ B g
  Con c    -> Con c
  Lam h s  -> Lam h $ exposeScope globals s
  App e1 e2 -> App (globals e1) (globals e2)
  Case e brs -> Case (globals e) (exposeBranches globals brs)

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  Var v >>= f = f v
  Global g >>= _ = Global g
  Con c >>= _ = Con c
  Lam h s >>= f = Lam h $ s >>>= f
  App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)
  Case e brs >>= f = Case (e >>= f) (brs >>>= f)

lamView :: Expr v -> Maybe (NameHint, (), Expr v, Scope1 Expr v)
lamView (Lam h s) = Just (h, (), Con mempty, s)
lamView _         = Nothing

etaLam :: Hint (Maybe Name) -> Scope1 Expr v -> Expr v
etaLam _ (Scope (App e (Var (B ()))))
  | B () `S.notMember` toSet (second (const ()) <$> e)
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n s = Lam n s

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c -> prettyM c
    (bindingsViewM lamView -> Just (hs, s)) -> parens `above` absPrec $
      withNameHints (Vector.fromList ((\(h, _, _) -> h) <$> hs)) $ \ns ->
        prettyM "\\" <> hsep (map prettyM $ Vector.toList ns) <> prettyM "." <+>
        associate (prettyM $ instantiate (pure . fromText . (ns Vector.!)) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 e2 -> prettyApp (prettyM e1) (prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+> prettyM "of" <$$> prettyM brs
