{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings, RankNTypes #-}
module Syntax.Data where

import Bound
import Bound.Var
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Annotation
import Syntax.Class
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

newtype DataDef typ v = DataDef { dataConstructors :: [ConstrDef (Scope Tele typ v)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

foldMapDataDef
  :: (Monoid m, Monad typ)
  => (forall v. typ v -> m)
  -> DataDef typ x
  -> m
foldMapDataDef f (DataDef cs) = foldMap (foldMap $ f . fromScope) cs

quantifiedConstrTypes
  :: (Eq v, Syntax typ)
  => DataDef typ v
  -> Telescope Scope Annotation typ v
  -> [ConstrDef (typ v)]
quantifiedConstrTypes (DataDef cs) ps = map (fmap $ \s -> pis ps s) cs

constrNames :: DataDef typ v -> [Constr]
constrNames = map constrName . dataConstructors

instance Bound DataDef where
  DataDef cs >>>= f = DataDef (fmap (>>>= f) <$> cs)

prettyDataDef
  :: (Eq1 typ, Eq v, IsString v, Monad typ, Pretty (typ v))
  => Telescope Scope Annotation typ v
  -> DataDef typ v
  -> PrettyM Doc
prettyDataDef ps (DataDef cs) = "data" <+> "_" <+> withTeleHints ps (\ns ->
    let inst = instantiate $ pure . fromText . (ns Vector.!) . unTele in
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

abstractDataDef :: Functor typ
                => (a -> Maybe b) -> DataDef typ a -> DataDef typ (Var b a)
abstractDataDef f (DataDef cs) = DataDef (fmap (fmap f') <$> cs)
  where
    f' a = maybe (F a) B $ f a

instantiateDataDef :: Monad typ
                   => (b -> typ a) -> DataDef typ (Var b a) -> DataDef typ a
instantiateDataDef f (DataDef cs) = DataDef (fmap (>>>= f') <$> cs)
  where
    f' = unvar f pure
