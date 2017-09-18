{-# LANGUAGE
  DeriveFoldable,
  DeriveFunctor,
  DeriveTraversable,
  GeneralizedNewtypeDeriving,
  OverloadedStrings,
  RankNTypes,
  TemplateHaskell
 #-}
module Syntax.Let where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Deriving
import Data.Functor.Classes
import Data.Hashable
import Data.Maybe
import Data.String
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Pretty
import Syntax.GlobalBind
import Syntax.Hint
import Syntax.Name
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
  :: (Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
  => Vector Name
  -> LetRec expr v
  -> PrettyM Doc
prettyLet ns (LetRec xs) = vcat $ imap go xs
  where
    go i (LetBinding _ s t)
      = n <+> ":" <+> prettyM t
      <$$> n <+> "=" <+> prettyM (instantiateLet (pure . fromName) ns s)
      where
        n = prettyM $ ns Vector.! i

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
instance (Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
  => Pretty (LetRec expr v) where
  prettyM letRec = withLetHints letRec $ \ns -> prettyLet ns letRec

instance GlobalBound LetRec where
  bound f g (LetRec xs)
    = LetRec $ (\(LetBinding h s t) -> LetBinding h (bound f g s) (bind f g t)) <$> xs

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
