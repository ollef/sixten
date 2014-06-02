{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Expr where

import Bound
import Control.Applicative
import Control.Monad.Error
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.Foldable
import Data.Function
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.STRef
import Data.Traversable
import Prelude.Extras

import qualified Core
import qualified Input
import Monad

type Input s = Input.Expr (MetaVar s)
type Core  s = Core.Expr  (MetaVar s)

data MetaVar s
  = Exists {metaId :: !Int, metaType :: Core s, metaRef :: STRef s (Maybe (Core s))}
  | Forall {metaId :: !Int, metaType :: Core s}

instance Eq (MetaVar s) where
  (==) = (==) `on` metaId

instance Ord (MetaVar s) where
  compare = compare `on` metaId

instance Show (MetaVar s) where
  showsPrec d (Exists i a _) = showParen (d > 10) $
    showString "Exists" . showChar ' ' . showsPrec 11 i .
    showChar ' ' . showsPrec 11 a . showChar ' ' . showString "<Ref>"
  showsPrec d (Forall i a) = showParen (d > 10) $
    showString "Forall" . showChar ' ' . showsPrec 11 i . showChar ' ' .
    showsPrec 11 a

freshExists :: Core s -> TCM s (MetaVar s)
freshExists a = do
  ref <- liftST $ newSTRef Nothing
  i   <- fresh
  return $ Exists i a ref

freshExistsV :: Monad g => Core s -> TCM s (g (MetaVar s))
freshExistsV a = return <$> freshExists a

freshForall :: Core s -> TCM s (MetaVar s)
freshForall a = do
  i <- fresh
  return $ Forall i a

freshForallV :: Monad g => Core s -> TCM s (g (MetaVar s))
freshForallV a = return <$> freshForall a

refine :: MetaVar s -> Core s -> TCM s ()
refine (Exists _ _ ref) x = liftST $ writeSTRef ref (Just x)
refine (Forall _ _)     _ = throwError "Trying to solve a forall meta variable"

solve :: MetaVar s -> Core s -> TCM s ()
solve v x = do
  whenM (isSolved v) $ throwError "Trying to solve something already solved"
  refine v x

solution :: MetaVar s f a -> TCM s (Maybe (f (MetaVar s f a)))
solution (Exists _ _ ref) = liftST $ readSTRef ref
solution (Forall _ _)     = return Nothing

isSolved :: MetaVar s f a -> TCM s Bool
isSolved v@(Exists _ _ _) = isJust <$> solution v
isSolved (Forall _ _)     = return False

isUnsolved :: MetaVar s f a -> TCM s Bool
isUnsolved v@(Exists _ _ _) = (not . isJust) <$> solution v
isUnsolved (Forall _ _)     = return False
--
-- inferLevel :: 

inferType :: Input s -> TCM s (Core s)
inferType expr = case expr of
  Input.Var v     -> return $ metaType v
  Input.Type n    -> return $ Core.Type $ n + 1
  Input.Pi s      -> do
    v <- freshExistsV
    let e = instantiate1 v s
    l2 <- inferLevel e
    l1 <- inferLevel v
  Input.Lam s     -> undefined
  Input.App e1 e2 -> undefined
  Input.Anno e t  -> undefined
  Input.Wildcard  -> undefined
