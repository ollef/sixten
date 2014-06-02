{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Input where

import Bound
import Control.Applicative
import Data.Foldable
import Data.Traversable
import Prelude.Extras

import Util

data Expr v
  = Var v
  | Type Int               -- ^ Type 0 : Type 1 : Type 2 : ...
  | Pi  (Scope1 Expr v)    -- ^ Dependent function space
  | Lam (Scope1 Expr v)
  | App (Expr v) (Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard               -- ^ Attempt to infer it
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
    Pi  s     -> Pi (s >>>= f)
    Lam s     -> Lam (s >>>= f)
    App e1 e2 -> App (e1 >>= f) (e2 >>= f)
    Anno e t  -> Anno (e >>= f) (t >>= f)
    Wildcard  -> Wildcard
