{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Lambda where
import Bound
import Control.Monad
import Data.Monoid
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Hint
import Pretty
import Util

data Expr v
  = Var v
  | Con Constr
  | Lam !NameHint (Scope1 Expr v)
  | App (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

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
  Con c >>= _ = Con c
  Lam h s >>= f = Lam h $ s >>>= f
  App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)

lamView :: Expr v -> Maybe (NameHint, (), Expr v, Scope1 Expr v)
lamView (Lam h s) = Just (h, (), Con mempty, s)
lamView _         = Nothing

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Con c -> prettyM c
    (bindingsViewM lamView -> Just (hs, s)) -> parens `above` absPrec $
      withNameHints (Vector.fromList ((\(h, _, _) -> h) <$> hs)) $ \ns ->
        prettyM "\\" <> hsep (map prettyM $ Vector.toList ns) <> prettyM "." <+>
        associate (prettyM $ instantiate (pure . fromText . (ns Vector.!)) s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 e2 -> prettyApp (prettyM e1) (prettyM e2)
