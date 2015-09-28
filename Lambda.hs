{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Lambda where
import Bound
import Control.Monad
import Data.Monoid
import Data.String
import Prelude.Extras

import Hint
import Pretty
import Util

data Expr v
  = Var v
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
  Lam h s >>= f = Lam h $ s >>>= f
  App e1 e2 >>= f = App (e1 >>= f) (e2 >>= f)

lamView :: Expr v -> Maybe (NameHint, Scope1 Expr v)
lamView (Lam h s) = Just (h, s)
lamView _         = Nothing

bindingsView
  :: (forall v'. Expr v' -> Maybe (NameHint, Scope1 Expr v'))
  -> Expr v -> Maybe ([NameHint], Scope Int Expr v)
bindingsView f expr@(f -> Just _) = Just $ go 0 $ F <$> expr
  where
    go x (f -> Just (n, s)) = (n : ns, s')
      where
        (ns, s') = (go $! (x + 1)) (instantiate1 (return $ B x) s)
    go _ e = ([], toScope e)
bindingsView _ _ = Nothing

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyPrec expr = case expr of
    Var v     -> prettyPrec v
    (bindingsView lamView -> Just (hs, s)) -> parens `above` absPrec $ withHints hs $ \f -> do
      ps <- associate $ prettyPrec $ instantiate (return . fromString . f) s
      return $ text "\\" <> hsep (zipWith (\x -> text . f . const x) [0..] hs)  <> text "." <+> ps
    Lam {} -> error "impossible prettyPrec lam"
    App e1 e2 -> prettyApp (prettyPrec e1) $ prettyPrec e2
