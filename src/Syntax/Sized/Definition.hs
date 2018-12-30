{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings #-}
module Syntax.Sized.Definition where

import Protolude

import Bound
import Control.Monad.Morph
import Data.Vector(Vector)

import FreeVar
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Sized.Anno
import Syntax.Telescope
import qualified TypedFreeVar as Typed

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
function
  :: Monad expr
  => Vector (FreeVar d, expr (FreeVar d))
  -> Anno expr (FreeVar d)
  -> Function expr (FreeVar d)
function vs = Function (varTelescope vs) . abstractAnno (teleAbstraction $ fst <$> vs)

functionTyped
  :: Monad expr
  => Vector (Typed.FreeVar () expr)
  -> Anno expr (Typed.FreeVar () expr)
  -> Function expr (Typed.FreeVar () expr)
functionTyped vs = Function (Typed.varTelescope vs) . abstractAnno (teleAbstraction vs)

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

instance Bound Constant where
  Constant expr >>>= f = Constant $ expr >>>= f

instance GBound Constant where
  gbound f (Constant expr) = Constant $ gbound f expr

instance Bound Function where
  Function args s >>>= f = Function (args >>>= f) (s >>>= f)

instance GBound Function where
  gbound f (Function args s) = Function (gbound f args) $ gbound f s

instance Bound Definition where
  FunctionDef vis cl fdef >>>= f = FunctionDef vis cl $ fdef >>>= f
  ConstantDef vis cdef >>>= f = ConstantDef vis $ cdef >>>= f
  AliasDef >>>= _ = AliasDef

instance GBound Definition where
  gbound f (FunctionDef vis cl fdef) = FunctionDef vis cl $ gbound f fdef
  gbound f (ConstantDef vis cdef) = ConstantDef vis $ gbound f cdef
  gbound _ AliasDef = AliasDef

instance (v ~ Doc, Pretty (expr v), Monad expr) => Pretty (Function expr v) where
  prettyM (Function vs s) = parens `above` absPrec $
    withNameHints (teleNames vs) $ \ns ->
      "\\" <> prettyTeleVars ns vs <> "." <+>
      associate absPrec (prettyM $ instantiateAnnoTele (pure . fromName) ns s)

instance PrettyAnnotation IsClosure where
  prettyAnnotation IsClosure = prettyTightApp "[]"
  prettyAnnotation NonClosure = identity

instance (v ~ Doc, Pretty (expr v)) => Pretty (Constant expr v) where
  prettyM (Constant e) = prettyM e

instance (v ~ Doc, Pretty (expr v), Monad expr) => Pretty (Definition expr v) where
  prettyM (ConstantDef v c) = prettyM v <+> prettyM c
  prettyM (FunctionDef v cl f) = prettyM v <+> prettyAnnotation cl (prettyM f)
  prettyM AliasDef = "alias"
