{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings #-}
module Syntax.Class where

import Bound
import Bound.Scope
import Control.Monad.Morph
import Data.Functor.Classes
import Data.String

import Error
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope
import Util

-------------------------------------------------------------------------------
-- Class definitions
newtype ClassDef typ v = ClassDef { classMethods :: [MethodDef (Scope TeleVar typ v)] }
  deriving (Foldable, Functor, Show, Traversable)

instance GlobalBound ClassDef where
  bound f g (ClassDef cs) = ClassDef $ fmap (bound f g) <$> cs

instance MFunctor ClassDef where
  hoist f (ClassDef cs) = ClassDef $ fmap (hoistScope f) <$> cs

methodNames :: ClassDef typ v -> [Name]
methodNames = map methodName . classMethods

prettyClassDef
  :: (Eq1 typ, Eq v, IsString v, Monad typ, Pretty (typ v))
  => PrettyM Doc
  -> Telescope Plicitness typ v
  -> ClassDef typ v
  -> PrettyM Doc
prettyClassDef name ps (ClassDef cs) = "class" <+> name <+> withTeleHints ps (\ns ->
    let inst = instantiateTele (pure . fromName) ns in
        prettyTeleVarTypes ns ps <+> "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) cs))
    )

data MethodDef typ = MethodDef
  { methodName :: !Name
  , methodLoc :: !SourceLoc
  , methodType :: typ
  } deriving (Foldable, Functor, Show, Traversable)

instance (IsString v, Pretty (typ v), Monad typ) => PrettyNamed (ClassDef typ v) where
  prettyNamed name (ClassDef cs) = "class" <+> name <+> "where" <$$>
    indent 2 (vcat (map (prettyM . fmap (instantiate $ pure . shower)) cs))

instance Pretty typ => Pretty (MethodDef typ) where
  prettyM (MethodDef n _ t) = prettyM n <+> ":" <+> prettyM t
