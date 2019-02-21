{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Context where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Effect.Fresh
import Syntax.Annotation
import Syntax.NameHint
import Util
import Util.Tsil(Tsil)
import qualified Util.Tsil as Tsil

newtype Var = Var Int
  deriving (Eq, Ord, Show, Hashable)

freeVar :: MonadFresh m => m Var
freeVar = Var <$> fresh

data Binding e = Binding
  { _hint :: !NameHint
  , _plicitness :: !Plicitness
  , _type :: e
  , _value :: !(Maybe e)
  } deriving (Functor, Foldable, Traversable, Show)

binding :: NameHint -> Plicitness -> e -> Binding e
binding h p t = Binding h p t Nothing

data Context e = Context
  { _vars :: Tsil Var
  , _varMap :: !(HashMap Var (Binding e))
  } deriving Functor

instance Foldable Context where
  foldMap f (Context vs m) = foldMap (foldMap f . (m HashMap.!)) vs

instance Traversable Context where
  traverse f (Context vs m)
    = Context vs . toHashMap
    <$> traverse (\v -> (,) v <$> traverse f (m HashMap.! v)) vs

fromList :: [(Var, Binding e)] -> Context e
fromList vs = Context (Tsil.fromList $ fst <$> vs) (toHashMap vs)

snoc :: Context e -> Var -> Binding e -> Context e
snoc (Context vs m) v b = Context (Tsil.Snoc vs v) (HashMap.insert v b m)

unsnoc :: Context e -> Maybe (Context e, (Var, Binding e))
unsnoc (Context Tsil.Nil _) = Nothing
unsnoc (Context (Tsil.Snoc vs v) m) = Just (Context vs $ HashMap.delete v m, (v, m HashMap.! v))

pattern (:>) :: Context e -> (Var, Binding e) -> Context e
pattern c :> vb <- (Syntax.Context.unsnoc -> Just (c, vb))
  where
    c :> (v, b) = snoc c v b

pattern Nil :: Context e
pattern Nil <- Context Tsil.Nil _
  where
    Nil = mempty

{-# COMPLETE (:>), Nil #-}

instance Semigroup (Context e) where
  Context vs1 m1 <> Context vs2 m2 = Context (vs1 <> vs2) (m1 <> m2)

instance Monoid (Context e) where
  mempty = Context mempty mempty

span :: (Var -> Binding e -> Bool) -> Context e -> (Context e, Context e)
span _ Nil = (Nil, Nil)
span p c@(c' :> (v, b))
  | p v b = second (:> (v, b)) $ span p c'
  | otherwise = (c, Nil)

splitAt :: Var -> Context e -> Maybe (Context e, Binding e, Context e)
splitAt v c = case span (\v' _ -> v /= v') c of
  (Nil, _) -> Nothing
  (c1 :> (_, b), c2) -> Just (c1, b, c2)
