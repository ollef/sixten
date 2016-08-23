{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, OverloadedStrings #-}
module Syntax.Definition where

import Bound
import Data.Bifoldable
import Data.Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HM
import Data.HashSet(HashSet)
import qualified Data.HashSet as HS
import Data.String
import Prelude.Extras

import Syntax.Class
import Syntax.Data
import Syntax.Name
import Syntax.Pretty
import TopoSort
import Util

data Definition expr v
  = Definition (expr v)
  | DataDefinition (DataDef expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

foldMapDefinition
  :: (Monoid m, Monad expr)
  => (forall v. expr v -> m)
  -> Definition expr x
  -> m
foldMapDefinition f (Definition e) = f e
foldMapDefinition f (DataDefinition d) = foldMapDataDef f d

prettyTypedDef
  :: (Eq1 expr, Eq v, IsString v, Monad expr, Pretty (expr v), SyntaxPi expr)
  => Definition expr v
  -> expr v
  -> PrettyM Doc
prettyTypedDef (Definition d) _ = prettyM d
prettyTypedDef (DataDefinition d) t = prettyDataDef (telescope t) d

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

instance (Monad expr, Pretty (expr v), IsString v) => Pretty (Definition expr v) where
  prettyM (Definition e) = prettyM e
  prettyM (DataDefinition d) = prettyM d

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

dependencies
  :: (Foldable e, Monad e)
  => (forall v. e v -> HashSet Constr)
  -> Program e Name
  -> HashMap Name (HashSet Name)
dependencies constrs prog =
  HM.map (bifoldMap toHashSet toHashSet) prog
  `union`
  HM.map (bifoldMap (foldMapDefinition constrs) constrs) prog
  `union`
  constrMappings
  where
    union = HM.unionWith HS.union
    constrMappings = HM.fromListWith mappend
      [ (c, HS.singleton n)
      | (n, (DataDefinition d, _)) <- HM.toList prog
      , c <- constrNames d
      ]

programConstrNames :: Program e v -> [Constr]
programConstrNames prog
  = [ c
    | (_, (DataDefinition d, _)) <- HM.toList prog
    , c <- constrNames d
    ]

dependencyOrder
  :: (Foldable e, Monad e)
  => (forall v. e v -> HashSet Constr)
  -> Program e Name
  -> [[(Name, (Definition e Name, e Name))]]
dependencyOrder constrs prog
  = fmap (\n -> (n, prog HM.! n)) . filter (`HM.member` prog)
  <$> topoSort (HM.toList $ dependencies constrs prog)
