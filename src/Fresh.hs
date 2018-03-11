{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Fresh where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Identity
import Control.Monad.Writer

import qualified LLVM.IRBuilder as IRBuilder

class Monad m => MonadFresh m where
  fresh :: m Int

  default fresh
    :: (MonadTrans t, MonadFresh m1, m ~ t m1)
    => m Int
  fresh = lift fresh


newtype Fresh a = Fresh (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

evalFresh :: Fresh a -> a
evalFresh (Fresh m) = evalState m 0

instance MonadFresh Fresh where
  fresh = do
    i <- get
    put $! i + 1
    return i

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadFresh m => MonadFresh (ReaderT r m)
instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m)
instance MonadFresh m => MonadFresh (StateT s m)
instance MonadFresh m => MonadFresh (IdentityT m)
instance MonadFresh m => MonadFresh (IRBuilder.IRBuilderT m)
instance MonadFresh m => MonadFresh (IRBuilder.ModuleBuilderT m)
