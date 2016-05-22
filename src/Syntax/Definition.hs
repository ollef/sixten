{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Data.Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.String
import Bound
import Prelude.Extras

import Syntax.Data
import Syntax.Name
import Syntax.Pretty
import Syntax.Telescope

data Definition expr v
  = Definition (expr v)
  | DataDefinition (DataDef expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

prettyTypedDef
  :: (Eq1 expr, Eq v, IsString v, Monad expr, Pretty (expr v))
  => Definition expr v
  -> expr v
  -> Telescope expr v
  -> PrettyM Doc
prettyTypedDef (Definition d) t _ = prettyM d <+> ":" <+> prettyM t
prettyTypedDef (DataDefinition d) t tele = prettyDataDef tele d <+> ":" <+> prettyM t

abstractDef
  :: Monad expr
  => (a -> Maybe b)
  -> Definition expr a
  -> Definition expr (Var b a)
abstractDef f (Definition d) = Definition $ fromScope $ abstract f d
abstractDef f (DataDefinition d) = DataDefinition $ abstractDataDef f d

instantiateDef :: Monad expr
               => (b -> expr a) -> Definition expr (Var b a) -> Definition expr a
instantiateDef f (Definition d) = Definition $ instantiate f $ toScope d
instantiateDef f (DataDefinition d) = DataDefinition $ instantiateDataDef f d

instance Bound Definition where
  Definition d >>>= f = Definition $ d >>= f
  DataDefinition d >>>= f = DataDefinition $ d >>>= f

recursiveAbstractDefs
  :: (Eq v, Monad f, Functor t, Foldable t, Hashable v)
  => t (v, Definition f v)
  -> t (Definition f (Var Int v))
recursiveAbstractDefs es = (abstractDef (`HM.lookup` vs) . snd) <$> es
  where
    vs = HM.fromList $ zip (toList $ fst <$> es) [(0 :: Int)..]

type Program expr v = HashMap Name (Definition expr v, expr v)
