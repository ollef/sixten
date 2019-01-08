{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax.Context where

import Protolude

import Bound
import Data.HashMap.Lazy as HashMap
import Data.Vector(Vector)
import Util.Tsil(Tsil)
import qualified Util.Tsil as Tsil

import Syntax.Annotation
import Syntax.NameHint

newtype FreeVar = FreeVar Int
  deriving (Eq, Ord, Show, Hashable)

data Binding e = Binding
  { _hint :: !NameHint
  , _plicitness :: !Plicitness
  , _type :: e
  , _value :: !(Maybe e)
  } deriving Show

instance Functor Binding where
  fmap f (Binding h p t v) = Binding h p (f t) (fmap f v)

data Context e = Context
  { _vars :: Tsil (FreeVar, Binding e)
  , _varMap :: !(HashMap FreeVar (Binding e))
  }

instance Functor Context where
  fmap f (Context vs m) = Context (fmap (fmap $ fmap f) vs) (fmap (fmap f) m)

(|>) :: Context e -> (FreeVar, Binding e) -> Context e
Context vs m |> (v, b) = Context (Tsil.Snoc vs (v, b)) (HashMap.insert v b m)

lookup :: FreeVar -> Context e -> Binding e
lookup v (Context _ m) = HashMap.lookupDefault (panic "lookup") v m
