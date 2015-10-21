{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable #-}
module Data where

import Bound
import Bound.Scope
import Bound.Var
import Data.Bitraversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Annotation
import Hint
import Pretty
import Util

data DataDef typ v = DataDef
  { dataParams       :: Vector (NameHint, Plicitness, Scope Int typ v)
  , dataConstructors :: [ConstrDef (Scope Int typ v)]
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

bitraverseDataDef :: (Applicative f, Bitraversable typ)
                  => (a -> f a')
                  -> (b -> f b')
                  -> DataDef (typ a) b
                  -> f (DataDef (typ a') b')
bitraverseDataDef f g (DataDef ps cs) =
  DataDef <$> traverse (\(h, p, s) -> (,,) h p <$> bitraverseScope f g s) ps
          <*> traverse (\(ConstrDef c t) -> ConstrDef c <$> bitraverseScope f g t) cs

instance Bound DataDef where
  DataDef ps cs >>>= f = DataDef ((\(h, p, s) -> (h, p, s >>>= f)) <$> ps)
                                 (fmap (>>>= f) <$> cs)

-- TODO
instance Pretty (DataDef typ v) where
  prettyM _ = prettyM "data ..."

dataType :: (Eq v, Monad typ)
         => DataDef typ v
         -> (NameHint -> Plicitness
                      -> typ (Var Int v)
                      -> Scope1 typ (Var Int v)
                      -> typ (Var Int v))
         -> Scope Int typ v
         -> typ v
dataType (DataDef params _) con inner
  = unvar (error "dataType") id <$> Vector.ifoldr f (fromScope inner) params
  where
    f i (h, p, t) rest = con h p (fromScope t) $ abstract1 (B i) rest

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

abstractDataDef :: Functor typ
                => (a -> Maybe b) -> DataDef typ a -> DataDef typ (Var b a)
abstractDataDef f (DataDef ps cs) = DataDef ((\(h, p, s) -> (h, p, fmap f' s)) <$> ps)
                                            (fmap (fmap f') <$> cs)
  where
    f' a = maybe (F a) B $ f a

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> prettyM ":" <+> prettyM t
