{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings, RankNTypes #-}
module Syntax.Data where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad.Morph
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes

import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope
import Util

newtype DataDef typ v = DataDef { dataConstructors :: [ConstrDef (Scope TeleVar typ v)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bound DataDef where
  DataDef cs >>>= f = DataDef $ fmap (>>>= f) <$> cs

instance GBound DataDef where
  gbound f (DataDef cs) = DataDef $ fmap (gbound f) <$> cs

instance MFunctor DataDef where
  hoist f (DataDef cs) = DataDef $ fmap (hoistScope f) <$> cs

bimapDataDef
  :: Bifunctor typ
  => (a -> a')
  -> (b -> b')
  -> DataDef (typ a) b
  -> DataDef (typ a') b'
bimapDataDef f g (DataDef cs) = DataDef $ fmap (bimapScope f g) <$> cs

bitraverseDataDef
  :: (Bitraversable typ, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> DataDef (typ a) b
  -> f (DataDef (typ a') b')
bitraverseDataDef f g (DataDef cs) = DataDef <$> traverse (traverse $ bitraverseScope f g) cs

transverseDataDef
  :: (Traversable typ, Monad f)
  => (forall r. typ r -> f (typ' r))
  -> DataDef typ a
  -> f (DataDef typ' a)
transverseDataDef f (DataDef cs) = DataDef <$> traverse (traverse $ transverseScope f) cs

constrNames :: DataDef typ v -> [Constr]
constrNames = map constrName . dataConstructors

prettyDataDef
  :: (Eq1 typ, Pretty (typ Doc), Monad typ)
  => PrettyM Doc
  -> Telescope Plicitness typ Doc
  -> DataDef typ Doc
  -> PrettyM Doc
prettyDataDef name ps (DataDef cs) = "type" <+> name <+> withTeleHints ps (\ns ->
    let inst = instantiateTele (pure . fromName) ns in
        prettyTeleVarTypes ns ps <+> "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) cs))
    )

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (v ~ Doc, Pretty (typ v), Monad typ) => PrettyNamed (DataDef typ v) where
  prettyNamed name (DataDef cs) = "type" <+> name <+> "where" <$$>
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
