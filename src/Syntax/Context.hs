{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Syntax.Context where

import Protolude

import Bound
import Data.HashMap.Lazy as HashMap
import Data.Vector(Vector)

import Effect.Fresh
import Syntax.Annotation
import Syntax.NameHint
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
  } deriving Show

binding :: NameHint -> Plicitness -> e -> Binding e
binding h p t = Binding h p t Nothing

instance Functor Binding where
  fmap f (Binding h p t v) = Binding h p (f t) (fmap f v)

data Context e = Context
  { _vars :: Tsil FreeVar
  , _varMap :: !(HashMap FreeVar (Binding e))
  }

instance Functor Context where
  fmap f (Context vs m) = Context vs (fmap (fmap f) m)

(|>) :: Context e -> (FreeVar, Binding e) -> Context e
Context vs m |> (v, b) = Context (Tsil.Snoc vs v) (HashMap.insert v b m)

instance Semigroup (Context e) where
  Context vs1 m1 <> Context vs2 m2 = Context (vs1 <> vs2) (m1 <> m2)

instance Monoid (Context e) where
  mempty = Context mempty mempty
