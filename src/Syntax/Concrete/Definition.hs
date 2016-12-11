{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GADTs #-}
module Syntax.Concrete.Definition where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.List.NonEmpty(NonEmpty)
import Data.Monoid
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Syntax.Concrete.Pattern
import Util

data PatDefinition expr v
  = PatDefinition (NonEmpty (DefLine expr v))
  | PatDataDefinition (DataDef expr v)
  deriving (Foldable, Functor, Show, Traversable)

data DefLine expr v
  = DefLine
    (Vector (Plicitness, Pat (PatternScope expr v) ()))
    (PatternScope expr v)
  deriving (Show)

-- TODO handle plicitness
etaExpandDefLine
  :: (Monad expr, AppSyntax expr, Annotation expr ~ Plicitness)
  => Int
  -> Annotation expr
  -> DefLine expr v
  -> DefLine expr v
etaExpandDefLine n anno (DefLine pats (Scope s))
  = DefLine pats' (Scope $ apps s $ (\i -> (anno, pure $ B i)) <$> Vector.enumFromN startIndex n)
  where
    startIndex = fromIntegral $ Vector.length patVars
    patVars = join $ toVector . snd <$> pats
    pats' = pats <> Vector.replicate n (anno, VarPat mempty ())

-------------------------------------------------------------------------------
-- Instances
instance Traversable expr => Functor (DefLine expr) where fmap = fmapDefault
instance Traversable expr => Foldable (DefLine expr) where foldMap = foldMapDefault

instance Traversable expr => Traversable (DefLine expr) where
  traverse f (DefLine pats s)
    = DefLine
    <$> traverse (traverse (bitraverse (traverse f) pure)) pats
    <*> traverse f s

instance GlobalBound PatDefinition where
  bound f g (PatDefinition defLines) = PatDefinition $ bound f g <$> defLines
  bound f g (PatDataDefinition dataDef) = PatDataDefinition $ bound f g dataDef

instance GlobalBound DefLine where
  bound f g (DefLine pats s) = DefLine (fmap (first (bound f g)) <$> pats) (bound f g s)
