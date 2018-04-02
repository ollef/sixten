{-# LANGUAGE
  DeriveFoldable,
  DeriveFunctor,
  DeriveTraversable,
  GADTs,
  GeneralizedNewtypeDeriving,
  OverloadedStrings,
  RankNTypes,
  TemplateHaskell
 #-}
module Syntax.Let where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Bitraversable
import Data.Deriving
import Data.Functor.Classes
import Data.Hashable
import Data.Maybe
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Pretty
import Syntax.GlobalBind
import Syntax.Name
import Syntax.NameHint
import Util

newtype LetVar = LetVar Int
  deriving (Eq, Enum, Hashable, Ord, Show, Num)

unLetVar :: LetVar -> Int
unLetVar (LetVar i) = i

newtype LetRec expr v = LetRec (Vector (LetBinding expr v))
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

unLetRec :: LetRec expr v -> Vector (LetBinding expr v)
unLetRec (LetRec xs) = xs

data LetBinding expr v = LetBinding !NameHint !(Scope LetVar expr v) (expr v)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

forLet
  :: LetRec expr v
  -> (NameHint -> Scope LetVar expr v -> expr v -> a)
  -> Vector a
forLet (LetRec xs) f = (\(LetBinding h s t) -> f h s t) <$> xs

iforLet
  :: LetRec expr v
  -> (Int -> NameHint -> Scope LetVar expr v -> expr v -> a)
  -> Vector a
iforLet (LetRec xs) f = imap (\i (LetBinding h s t) -> f i h s t) xs

letNameHints :: LetRec expr v -> Vector NameHint
letNameHints l = forLet l $ \h _ _ -> h

letBodies :: LetRec expr v -> Vector (Scope LetVar expr v)
letBodies l = forLet l $ \_ s _ -> s

letTypes :: LetRec expr v -> Vector (expr v)
letTypes l = forLet l $ \_ _ t -> t

forMLet
  :: Monad m
  => LetRec expr v
  -> (NameHint -> Scope LetVar expr v -> expr v -> m a)
  -> m (Vector a)
forMLet (LetRec xs) f = forM xs $ \(LetBinding h s t) -> f h s t

iforMLet
  :: Monad m
  => LetRec expr v
  -> (Int -> NameHint -> Scope LetVar expr v -> expr v -> m a)
  -> m (Vector a)
iforMLet (LetRec xs) f = iforM xs $ \i (LetBinding h s t) -> f i h s t

letNames :: LetRec expr v -> Vector NameHint
letNames (LetRec xs) = (\(LetBinding name _ _) -> name) <$> xs

withLetHints
  :: LetRec expr v
  -> (Vector Name -> PrettyM p)
  -> PrettyM p
withLetHints = withNameHints . letNames

instantiateLet
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope LetVar f a
  -> f a
instantiateLet f vs
  = instantiate (f . fromMaybe (error "instantiateLet") . (vs Vector.!?) . unLetVar)

letAbstraction :: (Eq a, Hashable a) => Vector a -> a -> Maybe LetVar
letAbstraction vs = fmap LetVar . hashedElemIndex vs

prettyLet
  :: (Eq1 expr, Pretty (expr Doc), Monad expr)
  => Vector Name
  -> LetRec expr Doc
  -> PrettyM Doc
prettyLet ns (LetRec xs) = vcat $ imap go xs
  where
    go i (LetBinding _ s t)
      = n <+> ":" <+> prettyM t
      <$$> n <+> "=" <+> prettyM (instantiateLet (pure . fromName) ns s)
      where
        n = prettyM $ ns Vector.! i

bitraverseLet
  :: (Bitraversable t, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> LetRec (t a) b
  -> f (LetRec (t a') b')
bitraverseLet f g (LetRec xs)
  = LetRec
  <$> traverse
    (\(LetBinding h s t) -> LetBinding h <$> bitraverseScope f g s <*> bitraverse f g t)
    xs

transverseLet
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> LetRec expr a
  -> f (LetRec expr' a)
transverseLet f (LetRec ds) = LetRec <$> traverse (transverseLetBinding f) ds

transverseLetBinding
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> LetBinding expr a
  -> f (LetBinding expr' a)
transverseLetBinding f (LetBinding h s t) = LetBinding h <$> transverseScope f s <*> f t

-------------------------------------------------------------------------------
-- Instances
instance (Eq1 expr, v ~ Doc, Pretty (expr v), Monad expr)
  => Pretty (LetRec expr v) where
  prettyM letRec = withLetHints letRec $ \ns -> prettyLet ns letRec

instance Bound LetRec where
  LetRec xs >>>= f
    = LetRec $ (\(LetBinding h s t) -> LetBinding h (s >>>= f) (t >>= f)) <$> xs

instance GBound LetRec where
  gbound f (LetRec xs)
    = LetRec $ (\(LetBinding h s t) -> LetBinding h (gbound f s) (gbind f t)) <$> xs

instance MFunctor LetRec where
  hoist f (LetRec xs)
    = LetRec $ (\(LetBinding h s t) -> LetBinding h (hoist f s) (f t)) <$> xs

$(return mempty)

instance (Eq1 expr, Monad expr) => Eq1 (LetRec expr) where
  liftEq = $(makeLiftEq ''LetRec)

instance (Ord1 expr, Monad expr) => Ord1 (LetRec expr) where
  liftCompare = $(makeLiftCompare ''LetRec)

instance (Show1 expr, Monad expr) => Show1 (LetRec expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LetRec)

instance (Eq1 expr, Monad expr) => Eq1 (LetBinding expr) where
  liftEq = $(makeLiftEq ''LetBinding)

instance (Ord1 expr, Monad expr) => Ord1 (LetBinding expr) where
  liftCompare = $(makeLiftCompare ''LetBinding)

instance (Show1 expr, Monad expr) => Show1 (LetBinding expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LetBinding)
