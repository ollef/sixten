{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, GADTs, OverloadedStrings #-}
module Syntax.Class where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Functor.Classes

import Error
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope

-------------------------------------------------------------------------------
-- Class definitions
data ClassDef typ v = ClassDef
  { classParams :: Telescope Plicitness typ v
  , classMethods :: [MethodDef (Scope TeleVar typ v)]
  }
  deriving (Foldable, Functor, Show, Traversable)

instance Bound ClassDef where
  ClassDef ps cs >>>= f = ClassDef (ps >>>= f) $ fmap (>>>= f) <$> cs

instance GBound ClassDef where
  gbound f (ClassDef ps cs) = ClassDef (gbound f ps) $ fmap (gbound f) <$> cs

instance MFunctor ClassDef where
  hoist f (ClassDef ps cs) = ClassDef (hoist f ps) $ fmap (hoistScope f) <$> cs

methodNames :: ClassDef typ v -> [Name]
methodNames = map methodName . classMethods

data MethodDef typ = MethodDef
  { methodName :: !Name
  , methodLoc :: !SourceLoc
  , methodType :: typ
  } deriving (Foldable, Functor, Show, Traversable)

instance (Eq1 typ, Monad typ, Pretty (typ v), v ~ Doc) => PrettyNamed (ClassDef typ v) where
  prettyNamed name (ClassDef ps cs) = "class" <+> name <+> withTeleHints ps (\ns ->
    let inst = instantiateTele (pure . fromName) ns in
        prettyTeleVarTypes ns ps <+> "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) cs))
    )

instance Pretty typ => Pretty (MethodDef typ) where
  prettyM (MethodDef n _ t) = prettyM n <+> ":" <+> prettyM t
