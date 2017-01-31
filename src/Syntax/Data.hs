{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings, RankNTypes #-}
module Syntax.Data where

import Bound
import Bound.Var
import Bound.Scope
import Data.Bifunctor
import Data.Bitraversable
import Data.String
import Prelude.Extras

import Syntax.Annotation
import Syntax.Class
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

newtype DataDef typ v = DataDef { dataConstructors :: [ConstrDef (Scope Tele typ v)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance GlobalBound DataDef where
  bound f g (DataDef cs) = DataDef $ fmap (bound f g) <$> cs

traverseDataDefFirst
  :: (Bitraversable typ, Applicative f)
  => (a -> f a')
  -> DataDef (typ a) v
  -> f (DataDef (typ a') v)
traverseDataDefFirst f (DataDef cs) = DataDef <$> traverse (traverse $ bitraverseScope f pure) cs

dataDefFirst
  :: Bifunctor typ
  => (a -> a')
  -> DataDef (typ a) v
  -> DataDef (typ a') v
dataDefFirst f (DataDef cs) = DataDef $ map (fmap $ bimapScope f id) cs

quantifiedConstrTypes
  :: Syntax typ
  => DataDef typ v
  -> typ v
  -> (Annotation typ -> Annotation typ)
  -> [ConstrDef (typ v)]
quantifiedConstrTypes (DataDef cs) typ anno = map (fmap $ pis ps) cs
  where
    ps = mapAnnotations anno $ telescope typ

constrNames :: DataDef typ v -> [Constr]
constrNames = map constrName . dataConstructors

prettyDataDef
  :: (Eq1 typ, Eq v, IsString v, Monad typ, Pretty (typ v), Eq (Annotation typ), PrettyAnnotation (Annotation typ))
  => Telescope (Annotation typ) typ v
  -> DataDef typ v
  -> PrettyM Doc
prettyDataDef ps (DataDef cs) = "data" <+> "_" <+> withTeleHints ps (\ns ->
    let inst = instantiateTele (pure . fromName) ns in
        prettyTeleVarTypes ns ps <+> "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) cs))
    )

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (IsString v, Pretty (typ v), Monad typ) => Pretty (DataDef typ v) where
  prettyM (DataDef cs) = "data" <+> "_" <+> "where" <$$>
    indent 2 (vcat (map (prettyM . fmap (instantiate $ pure . shower)) cs))

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> ":" <+> prettyM t

abstractDataDef
  :: Functor typ
  => (a -> Maybe b)
  -> DataDef typ a
  -> DataDef typ (Var b a)
abstractDataDef f (DataDef cs) = DataDef (fmap (fmap f') <$> cs)
  where
    f' a = maybe (F a) B $ f a

instantiateDataDef
  :: Monad typ
  => (b -> typ a)
  -> DataDef typ (Var b a)
  -> DataDef typ a
instantiateDataDef f (DataDef cs) = DataDef (fmap (>>>= f') <$> cs)
  where
    f' = unvar f pure
