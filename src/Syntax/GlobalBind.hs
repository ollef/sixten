{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Syntax.GlobalBind where

import Syntax.Binds
import Bound.Var
import Data.Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet

import Syntax.Module

class (Monad m, Functor f) => BindsGlobal m f | f -> m where
  -- | Perform substitution on globals inside a structure
  bind :: (QName -> m a) -> f a -> f a

instance (BindsGlobal m m, BindsGlobal m f) => BindsGlobal m (Scope m b f) where
  bind f (Scope s) = Scope $ fmap (fmap $ bind f) $ bind (fmap (F . pure) . f) s

-- globals :: (Foldable e, GlobalBind e) => e v -> HashSet QName
-- globals = fold . bind (pure . const mempty) (pure . HashSet.singleton)

-- boundGlobals :: (Foldable (t e), GlobalBind e, GlobalBound t) => t e v -> HashSet QName
-- boundGlobals = fold . bound (pure . const mempty) (pure . HashSet.singleton)

-- traverseGlobals
--   :: (GlobalBound t, GlobalBind e, Traversable (t e), Applicative f)
--   => (QName -> f QName)
--   -> t e a
--   -> f (t e a)
-- traverseGlobals f
--   = fmap (bound (unvar pure global) global)
--   . sequenceA
--   . bound (pure . pure . B) (pure . fmap F . f)
