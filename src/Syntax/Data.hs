{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Syntax.Data where

import Bound
import Bound.Scope
import Bound.Var
import Data.Bitraversable
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Annotation
import Syntax.Hint
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope
import Util

newtype DataDef typ v = DataDef { dataConstructors :: [ConstrDef (Scope Tele typ v)] }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

quantifiedConstrTypes :: (Eq v, Monad typ)
                      => (NameHint -> d
                                   -> typ (Var Tele v)
                                   -> Scope1 typ (Var Tele v)
                                   -> typ (Var Tele v))
                      -> DataDef typ v
                      -> Telescope d typ v
                      -> [ConstrDef (typ v)]
quantifiedConstrTypes pifun (DataDef cs) ps = map (fmap $ \s -> quantify pifun s ps) cs

constructorNames :: DataDef typ v -> [Constr]
constructorNames = map constrName . dataConstructors

bitraverseDataDef :: (Applicative f, Bitraversable typ)
                  => (a -> f a')
                  -> (b -> f b')
                  -> DataDef (typ a) b
                  -> f (DataDef (typ a') b')
bitraverseDataDef f g (DataDef cs) =
  DataDef <$> traverse (\(ConstrDef c t) -> ConstrDef c <$> bitraverseScope f g t) cs

instance Bound DataDef where
  DataDef cs >>>= f = DataDef (fmap (>>>= f) <$> cs)

prettyDataDef :: (Eq1 typ, Eq v, Eq d, HasRelevance d, HasPlicitness d, IsString v, Monad typ, Pretty (typ v))
              => Telescope d typ v -> DataDef typ v -> PrettyM Doc
prettyDataDef ps (DataDef cs) = prettyM "data" <+> prettyM "_" <+> withTeleHints ps (\ns ->
    let inst = instantiate $ pure . fromText . (ns Vector.!) . unTele in
        prettyTeleVarTypes ns ps <+> prettyM "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) cs))
    )

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> prettyM ":" <+> prettyM t

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
