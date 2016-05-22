{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, OverloadedStrings #-}
module Syntax.Data where

import Bound
import Bound.Var
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Class
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

newtype DataDef typ v = DataDef { dataConstructors :: [ConstrDef (Scope Tele typ v)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

quantifiedConstrTypes
  :: (Eq v, Syntax typ)
  => DataDef typ v
  -> Telescope typ v
  -> [ConstrDef (typ v)]
quantifiedConstrTypes (DataDef cs) ps = map (fmap $ \s -> pis ps s) cs

constructorNames :: DataDef typ v -> [Constr]
constructorNames = map constrName . dataConstructors

instance Bound DataDef where
  DataDef cs >>>= f = DataDef (fmap (>>>= f) <$> cs)

prettyDataDef
  :: (Eq1 typ, Eq v, IsString v, Monad typ, Pretty (typ v))
  => Telescope typ v
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
