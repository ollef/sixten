{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module TypedFreeVar where

-- import Prelude(showsPrec, showParen, showString, showChar)
-- import Protolude

-- import Bound
-- import Data.Char
-- import Data.Functor.Classes
-- import qualified Data.HashSet as HashSet
-- import Data.IORef
-- import qualified Data.Text as Text
-- import Data.Vector(Vector)

-- import Effect
-- import Pretty
-- import Syntax.Annotation
-- import Syntax.Let
-- import Syntax.Name
-- import Syntax.NameHint
-- import Syntax.Telescope
-- import Util

-- newtype FreeVar = FreeVar
--   { _varId :: Int
--   } deriving (Eq, Ord, Show, Hashable)

-- data VarInfo e = VarInfo
--   { _var :: !FreeVar
--   , _hint :: !NameHint
--   , _plicitness :: !Plicitness
--   , _type :: e FreeVar
--   , _value :: !(Maybe (e FreeVar))
--   } deriving Show

-- instance (Show d, Show1 e) => Show (VarInfo d e) where
--   showsPrec d (VarInfo (FreeVar i) h p t v) = showParen (d > 10) $
--     showString "VarInfo" .
--     showChar ' ' . showsPrec 11 i .
--     showChar ' ' . showsPrec 11 h .
--     showChar ' ' . showsPrec 11 p .
--     showChar ' ' . showsPrec1 11 t
--     showChar ' ' . showsPrec1 11 v

-- instance Pretty (VarInfo d e) where
--   pretty (VarInfo (FreeVar i) h _ _ _)
--     | Text.null hintText = "$" <> shower i
--     | isDigit (Text.last hintText) = "$" <> hint <> "-" <> shower i
--     | otherwise = "$" <> hint <> shower i
--     where
--       hintText = fromNameHint mempty fromName h
--       hint = pretty hintText

-- freeVar
--   :: MonadFresh m
--   => m FreeVar
-- freeVar = FreeVar <$> fresh

-- -- | Like freeVar, but with logging. TODO merge with freeVar?
-- forall
--   :: (MonadFresh m, MonadLog m)
--   => m FreeVar
-- forall = do
--   v <- freeVar
--   logCategory "forall" $ "forall: " <> shower (_varId v)
--   return v

-- extendContext
--   :: (MonadFresh m, MonadLog m, MonadContext (VarInfo d e) m)
--   => NameHint
--   -> d
--   -> e FreeVar
--   -> (FreeVar -> m a)
--   -> m a
-- extendContext h p t k = do
--   v <- forall
--   withVar (VarInfo v h p t) $ k v

-- teleExtendContext
--   :: (MonadFresh m, MonadLog m, MonadContext (VarInfo d e) m, Monad e)
--   => Telescope d e FreeVar
--   -> (Vector FreeVar -> m a)
--   -> m a
-- teleExtendContext tele k = do
--   vs <- forTeleWithPrefixM tele $ \h p s vs -> do
--     let e = instantiateTele pure vs s
--     forall h p e
--   withVars vs $ k vs

-- teleMapExtendContext
--   :: (MonadFresh m, MonadLog m, MonadContext (VarInfo d e') m, Monad e)
--   => Telescope d e FreeVar
--   -> (e FreeVar -> m (e' FreeVar))
--   -> (Vector FreeVar -> m a)
--   -> m a
-- teleMapExtendContext tele f k = do
--   vs <- forTeleWithPrefixM tele $ \h p s vs -> do
--     let e = instantiateTele pure vs s
--     e' <- withVars vs $ f e
--     forall h p e'
--   withVars vs $ k vs

-- letExtendContext
--   :: (MonadFresh m, MonadLog m, MonadContext (VarInfo Plicitness e) m)
--   => LetRec e (VarInfo Plicitness e)
--   -> (Vector (VarInfo Plicitness e) -> m a)
--   -> m a
-- letExtendContext ds k = do
--   vs <- forMLet ds $ \h _ _ t ->
--     forall h Explicit t
--   withVars vs $ k vs

-- letMapExtendContext
--   :: (MonadFresh m, MonadLog m, MonadContext (VarInfo Plicitness e') m)
--   => LetRec e FreeVar
--   -> (e FreeVar -> m (e' FreeVar))
--   -> (Vector FreeVar -> m a)
--   -> m a
-- letMapExtendContext tele f k = do
--   vs <- forMLet tele $ \h _ _ t -> do
--     t' <- f t
--     forall h Explicit t'
--   withVars vs $ k vs

-- letVar
--   :: (MonadFresh m, MonadIO m)
--   => NameHint
--   -> d
--   -> e FreeVar
--   -> m (VarInfo d e, e FreeVar -> m ())
-- letVar h d t = do
--   i <- fresh
--   ref <- liftIO $ newIORef Nothing
--   return (VarInfo (FreeVar i) h d (Just ref) t, liftIO . writeIORef ref . Just)

-- showFreeVar
--   :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc))
--   => f (FreeVar d e)
--   -> Doc
-- showFreeVar x = do
--   let vs = toHashSet x
--   let shownVars = [(pretty v, pretty $ pretty <$> varType v) | v <- HashSet.toList vs]
--   pretty (pretty <$> x)
--     <> if null shownVars
--       then mempty
--       else ", free vars: " <> pretty shownVars

-- logFreeVar
--   :: (Functor e, Functor f, Foldable f, Pretty (f Doc), Pretty (e Doc), MonadLog m)
--   => Category
--   -> Text
--   -> f (FreeVar d e)
--   -> m ()
-- logFreeVar c@(Category ct) s x = whenLoggingCategory c $ do
--   let r = showFreeVar x
--   Effect.log $ "[" <> ct <> "] " <> s <> ": " <> showWide r

-- varTelescope
--   :: Monad e
--   => Vector (FreeVar d e)
--   -> Telescope d e (FreeVar d e)
-- varTelescope vs
--   = Telescope
--   $ (\v -> TeleArg (varHint v) (varData v) $ abstract abstr $ varType v)
--   <$> vs
--   where
--     abstr = teleAbstraction vs

-- varTypeTelescope
--   :: Monad e'
--   => Vector (FreeVar d e, e' (FreeVar d e))
--   -> Telescope () e' (FreeVar d e)
-- varTypeTelescope vs
--   = Telescope
--   $ (\(v, t) -> TeleArg (varHint v) () $ abstract abstr t)
--   <$> vs
--   where
--     abstr = teleAbstraction (fst <$> vs)
