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

fromList :: [(FreeVar, Binding e)] -> Context e
fromList vs = Context (Tsil.fromList $ fst <$> vs) (toHashMap vs)

snoc :: Context e -> FreeVar -> Binding e -> Context e
snoc (Context vs m) v b = Context (Tsil.Snoc vs v) (HashMap.insert v b m)

unsnoc :: Context e -> Maybe (Context e, (FreeVar, Binding e))
unsnoc (Context Tsil.Nil _) = Nothing
unsnoc (Context (Tsil.Snoc vs v) m) = Just (Context vs $ HashMap.delete v m, (v, m HashMap.! v))

pattern (:>) :: Context e -> (FreeVar, Binding e) -> Context e
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

span :: (FreeVar -> Binding e -> Bool) -> Context e -> (Context e, Context e)
span _ Nil = (Nil, Nil)
span p c@(c' :> (v, b))
  | p v b = second (:> (v, b)) $ span p c'
  | otherwise = (c, Nil)

splitAt :: FreeVar -> Context e -> Maybe (Context e, Binding e, Context e)
splitAt v c = case span (\v' _ -> v /= v') c of
  (Nil, _) -> Nothing
  (c1 :> (_, b), c2) -> Just (c1, b, c2)
