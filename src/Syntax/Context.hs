{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Context where

import Protolude

import Data.HashMap.Lazy as HashMap

import Effect.Fresh
import Syntax.Annotation
import Syntax.NameHint
import Util
import Util.Tsil(Tsil)
import qualified Util.Tsil as Tsil

newtype FreeVar = FreeVar Int
  deriving (Eq, Ord, Show, Hashable)

freeVar :: MonadFresh m => m FreeVar
freeVar = FreeVar <$> fresh

data Binding e = Binding
  { _hint :: !NameHint
  , _plicitness :: !Plicitness
  , _type :: e
  , _value :: !(Maybe e)
  } deriving (Functor, Foldable, Traversable, Show)

binding :: NameHint -> Plicitness -> e -> Binding e
binding h p t = Binding h p t Nothing

data Context e = Context
  { _vars :: Tsil FreeVar
  , _varMap :: !(HashMap FreeVar (Binding e))
  } deriving Functor

instance Foldable Context where
  foldMap f (Context vs m) = foldMap (foldMap f . (m HashMap.!)) vs

instance Traversable Context where
  traverse f (Context vs m)
    = Context vs . toHashMap
    <$> traverse (\v -> (,) v <$> traverse f (m HashMap.! v)) vs

(|>) :: Context e -> (FreeVar, Binding e) -> Context e
Context vs m |> (v, b) = Context (Tsil.Snoc vs v) (HashMap.insert v b m)

instance Semigroup (Context e) where
  Context vs1 m1 <> Context vs2 m2 = Context (vs1 <> vs2) (m1 <> m2)

instance Monoid (Context e) where
  mempty = Context mempty mempty
