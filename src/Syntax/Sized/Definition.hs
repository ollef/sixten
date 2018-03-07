{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings #-}
module Syntax.Sized.Definition where

import Control.Monad.Morph
import Data.Monoid
import Data.Void

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Module
import Syntax.Name
import Syntax.Sized.Anno
import Syntax.Telescope
import Util.TopoSort

data Function expr v
  = Function (Telescope () expr v) (AnnoScope TeleVar expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Constant expr v
  = Constant (Anno expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data IsClosure
  = NonClosure
  | IsClosure
  deriving (Eq, Ord, Show)

data Definition expr v
  = FunctionDef Visibility IsClosure (Function expr v)
  | ConstantDef Visibility (Constant expr v)
  | AliasDef
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-------------------------------------------------------------------------------
-- Helpers
dependencyOrder
  :: (GlobalBind expr, Foldable expr)
  => [(QName, Definition expr Void)]
  -> [[(QName, Definition expr Void)]]
dependencyOrder = fmap flattenSCC . topoSortWith fst (bound absurd pure . snd)

-------------------------------------------------------------------------------
-- Instances
instance MFunctor Constant where
  hoist f (Constant e) = Constant (hoist f e)

instance MFunctor Function where
  hoist f (Function tele s) = Function (hoist f tele) (hoist f s)

instance MFunctor Definition where
  hoist f (FunctionDef vis cl fdef) = FunctionDef vis cl $ hoist f fdef
  hoist f (ConstantDef vis cdef) = ConstantDef vis $ hoist f cdef
  hoist _ AliasDef = AliasDef

instance GlobalBound Constant where
  bound f g (Constant expr) = Constant $ bound f g expr

instance GlobalBound Function where
  bound f g (Function args s) = Function (bound f g args) $ bound f g s

instance GlobalBound Definition where
  bound f g (FunctionDef vis cl fdef) = FunctionDef vis cl $ bound f g fdef
  bound f g (ConstantDef vis cdef) = ConstantDef vis $ bound f g cdef
  bound _ _ AliasDef = AliasDef

instance (v ~ Doc, Pretty (expr v), Monad expr) => Pretty (Function expr v) where
  prettyM (Function vs s) = parens `above` absPrec $
    withNameHints (teleNames vs) $ \ns ->
      "\\" <> prettyTeleVars ns vs <> "." <+>
      associate absPrec (prettyM $ instantiateAnnoTele (pure . fromName) ns s)

instance PrettyAnnotation IsClosure where
  prettyAnnotation IsClosure = prettyTightApp "[]"
  prettyAnnotation NonClosure = id

instance (v ~ Doc, Pretty (expr v)) => Pretty (Constant expr v) where
  prettyM (Constant e) = prettyM e

instance (v ~ Doc, Pretty (expr v), Monad expr) => Pretty (Definition expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v cl f) = prettyM v <+> prettyAnnotation cl (prettyM f)
  prettyM AliasDef = "alias"
