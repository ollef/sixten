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

data DataDef d typ v = DataDef
  { dataParams       :: Telescope d typ v
  , dataConstructors :: [ConstrDef (Scope Tele typ v)]
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

quantifiedConstrTypes :: (Eq v, Monad typ)
                      => (NameHint -> d
                                   -> typ (Var Tele v)
                                   -> Scope1 typ (Var Tele v)
                                   -> typ (Var Tele v))
                      -> DataDef d typ v
                      -> [ConstrDef (typ v)]
quantifiedConstrTypes pifun (DataDef ps cs) = map (fmap $ quantify pifun ps) cs

constructorNames :: DataDef d typ v -> [Constr]
constructorNames = map constrName . dataConstructors

tritraverseDataDef :: (Applicative f, Bitraversable typ)
                  => (d -> f d')
                  -> (a -> f a')
                  -> (b -> f b')
                  -> DataDef d (typ a) b
                  -> f (DataDef d' (typ a') b')
tritraverseDataDef e f g (DataDef ps cs) =
  DataDef <$> tritraverseTelescope e f g ps
          <*> traverse (\(ConstrDef c t) -> ConstrDef c <$> bitraverseScope f g t) cs

instance Bound (DataDef d) where
  DataDef ps cs >>>= f = DataDef (ps >>>= f) (fmap (>>>= f) <$> cs)

instance (Eq1 typ, Eq v, Eq d, HasRelevance d, HasPlicitness d, IsString v, Monad typ, Pretty (typ v)) => Pretty (DataDef d typ v) where
  prettyM (DataDef ps ts) = prettyM "data" <+> prettyM "_" <+> withTeleHints ps (\ns ->
    let inst = instantiate $ pure . fromText . (ns Vector.!) . unTele in
        prettyTeleVarTypes ns ps <+> prettyM "where" <$$>
          indent 2 (vcat (map (prettyM . fmap inst) ts))
    )

dataType :: (Eq v, Monad typ)
         => DataDef d typ v
         -> (NameHint -> d
                      -> typ (Var Tele v)
                      -> Scope1 typ (Var Tele v)
                      -> typ (Var Tele v))
         -> Scope Tele typ v
         -> typ v
dataType (DataDef (Telescope params) _) con inner
  = unvar (error "dataType") id <$> Vector.ifoldr f (fromScope inner) params
  where
    f i (h, p, t) rest = con h p (fromScope t) $ abstract1 (B $ Tele i) rest

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> prettyM ":" <+> prettyM t

abstractDataDef :: Functor typ
                => (a -> Maybe b) -> DataDef d typ a -> DataDef d typ (Var b a)
abstractDataDef f (DataDef ps cs) = DataDef (f' <$> ps)
                                            (fmap (fmap f') <$> cs)
  where
    f' a = maybe (F a) B $ f a

instantiateDataDef :: Monad typ
                   => (b -> typ a) -> DataDef d typ (Var b a) -> DataDef d typ a
instantiateDataDef f (DataDef ps cs) = DataDef (ps >>>= f')
                                               (fmap (>>>= f') <$> cs)
  where
    f' = unvar f pure
