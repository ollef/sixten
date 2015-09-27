{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Lambda where
import Bound
import Control.Monad
import Prelude.Extras

import Hint
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
