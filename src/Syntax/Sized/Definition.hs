{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings #-}
module Syntax.Sized.Definition where

import Bound
import Control.Monad.Morph
import Data.Foldable
import Data.Monoid
import Data.String
import Data.Void

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Module
import Syntax.Name
import Syntax.Telescope
import Util.TopoSort

data Function expr v
  = Function (Telescope () expr v) (Scope Tele expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Constant expr v
  = Constant (expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data IsClosure
  = NonClosure
  | IsClosure
  deriving (Eq, Ord, Show)

data Definition expr v
  = FunctionDef Visibility IsClosure (Function expr v)
  | ConstantDef Visibility (Constant expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
dependencyOrder
  :: (GlobalBind expr, Foldable expr)
  => [(QName, Definition expr Void)]
  -> [[(QName, Definition expr Void)]]
dependencyOrder = topoSortWith fst (toList . bound absurd pure . snd)

-------------------------------------------------------------------------------
-- Instances
instance MFunctor Constant where
  hoist f (Constant e) = Constant (f e)

instance MFunctor Function where
  hoist f (Function tele s) = Function (hoist f tele) (hoist f s)

instance MFunctor Definition where
  hoist f (FunctionDef vis cl fdef) = FunctionDef vis cl $ hoist f fdef
  hoist f (ConstantDef vis cdef) = ConstantDef vis $ hoist f cdef

instance GlobalBound Constant where
  bound f g (Constant expr) = Constant $ bind f g expr

instance GlobalBound Function where
  bound f g (Function args s) = Function (bound f g args) $ bound f g s

instance GlobalBound Definition where
  bound f g (FunctionDef vis cl fdef) = FunctionDef vis cl $ bound f g fdef
  bound f g (ConstantDef vis cdef) = ConstantDef vis $ bound f g cdef

instance (Eq v, IsString v, Pretty v, Pretty (expr v), Monad expr)
  => Pretty (Function expr v) where
  prettyM (Function vs s) = parens `above` absPrec $
    withNameHints (teleNames vs) $ \ns ->
      "\\" <> prettyTeleVars ns vs <> "." <+>
      associate absPrec (prettyM $ instantiateTele (pure . fromName) ns s)

instance PrettyAnnotation IsClosure where
  prettyAnnotation IsClosure = prettyTightApp "[]"
  prettyAnnotation NonClosure = id

instance (Eq v, IsString v, Pretty v, Pretty (expr v))
  => Pretty (Constant expr v) where
  prettyM (Constant e) = prettyM e

instance (Eq v, IsString v, Pretty v, Pretty (expr v), Monad expr)
  => Pretty (Definition expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v cl f) = prettyM v <+> prettyAnnotation cl (prettyM f)
