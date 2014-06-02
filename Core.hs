{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Core where

import Bound
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Prelude.Extras

import Util

data Expr v
  = Var v
  | Type Int
  | Pi  (Expr v) (Scope1 Expr v)
  | Lam (Expr v) (Scope1 Expr v)
  | App (Expr v) (Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Eq1 Expr; instance Ord1 Expr; instance Show1 Expr

instance Applicative Expr where
  pure = return
  ef <*> ex = do f <- ef; x <- ex; return $ f x

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v     -> f v
    Type n    -> Type n
    Pi  t s   -> Pi (t >>= f) (s >>>= f)
    Lam t s   -> Lam (t >>= f) (s >>>= f)
    App e1 e2 -> App (e1 >>= f) (e2 >>= f)
