{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE GADTs #-}
module MonadLog where

import Protolude

import Control.Monad.Except
import Control.Monad.Trans.Identity
import Control.Monad.Writer
import Data.Text(Text)
import qualified LLVM.IRBuilder as IRBuilder

class Monad m => MonadLog m where
  log :: Text -> m ()
  default log :: (MonadTrans t, MonadLog m1, m ~ t m1) => Text -> m ()
  log = lift . MonadLog.log

  verbosity :: m Int

  default verbosity :: (MonadTrans t, MonadLog m1, m ~ t m1) => m Int
  verbosity = lift verbosity

whenVerbose :: MonadLog m => Int -> m () -> m ()
whenVerbose i m = do
  v <- verbosity
  when (v >= i) m

logVerbose :: MonadLog m => Int -> Text -> m ()
logVerbose i = whenVerbose i . MonadLog.log

-------------------------------------------------------------------------------
-- mtl instances
-------------------------------------------------------------------------------
instance MonadLog m => MonadLog (ReaderT r m)
instance (Monoid w, MonadLog m) => MonadLog (WriterT w m)
instance MonadLog m => MonadLog (StateT s m)
instance MonadLog m => MonadLog (IdentityT m)
instance MonadLog m => MonadLog (IRBuilder.IRBuilderT m)
instance MonadLog m => MonadLog (IRBuilder.ModuleBuilderT m)
instance MonadLog m => MonadLog (ExceptT e m)
