{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Syntax.Data where

import Protolude

import Bound hiding (Var)
import Bound.Scope
import Control.Monad.Morph
import Data.Bitraversable
import Data.Deriving
import Data.Functor.Classes
import Data.Hashable.Lifted
import Data.Vector(Vector)

import Effect.Context as Context
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope
import Util

data DataDef typ v = DataDef
  { dataBoxiness :: !Boxiness
  , dataParams :: Telescope typ v
  , dataConstructors :: [ConstrDef (Scope TeleVar typ v)]
  } deriving (Eq, Ord, Show, Foldable, Functor, Traversable, Generic, Hashable, Generic1, Hashable1)

dataDef
  :: (Monad typ, MonadContext (typ Var) m)
  => Boxiness
  -> Vector Var
  -> [ConstrDef (typ Var)]
  -> m (DataDef typ Var)
dataDef b vs cs = do
  tele <- varTelescope vs
  return $ DataDef b tele $ fmap abstr <$> cs
  where
    abstr = abstract $ teleAbstraction vs

plicitDataDef
  :: (Monad typ, MonadContext (typ Var) m)
  => Boxiness
  -> Vector (Plicitness, Var)
  -> [ConstrDef (typ Var)]
  -> m (DataDef typ Var)
plicitDataDef b pvs cs = do
  tele <- plicitVarTelescope pvs
  return $ DataDef b tele $ fmap abstr <$> cs
  where
    abstr = abstract $ teleAbstraction $ snd <$> pvs

instance Bound DataDef where
  DataDef b ps cs >>>= f = DataDef b (ps >>>= f) $ fmap (>>>= f) <$> cs

instance GBound DataDef where
  gbound f (DataDef b ps cs) = DataDef b (gbound f ps) $ fmap (gbound f) <$> cs

instance MFunctor DataDef where
  hoist f (DataDef b ps cs) = DataDef b (hoist f ps) $ fmap (hoistScope f) <$> cs

bimapDataDef
  :: Bifunctor typ
  => (a -> a')
  -> (b -> b')
  -> DataDef (typ a) b
  -> DataDef (typ a') b'
bimapDataDef f g (DataDef b ps cs) = DataDef b (bimapTelescope f g ps) $ fmap (bimapScope f g) <$> cs

bitraverseDataDef
  :: (Bitraversable typ, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> DataDef (typ a) b
  -> f (DataDef (typ a') b')
bitraverseDataDef f g (DataDef b ps cs) = DataDef b <$> bitraverseTelescope f g ps <*> traverse (traverse $ bitraverseScope f g) cs

transverseDataDef
  :: (Traversable typ, Monad f)
  => (forall r. typ r -> f (typ' r))
  -> DataDef typ a
  -> f (DataDef typ' a)
transverseDataDef f (DataDef b ps cs) = DataDef b <$> transverseTelescope f ps <*> traverse (traverse $ transverseScope f) cs

constrNames :: DataDef typ v -> [Constr]
constrNames = map constrName . dataConstructors

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable, Generic, Hashable, Generic1, Hashable1)

instance (v ~ Doc, Pretty (typ v), Monad typ, Eq1 typ) => PrettyNamed (DataDef typ v) where
  prettyNamed name (DataDef b ps cs) = withTeleHints ps $ \ns -> do
    let inst = instantiateTele (pure . fromName) ns
    prettyM b <+> "type" <+> name <+> prettyTeleVarTypes ns ps <+> "where" <$$>
      indent 2 (vcat $ map (prettyM . fmap inst) cs)

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> ":" <+> prettyM t

deriveEq1 ''ConstrDef
deriveOrd1 ''ConstrDef
deriveShow1 ''ConstrDef
instance (Eq1 typ, Monad typ) => Eq1 (DataDef typ) where
  liftEq = $(makeLiftEq ''DataDef)
instance (Ord1 typ, Monad typ) => Ord1 (DataDef typ) where
  liftCompare = $(makeLiftCompare ''DataDef)
instance (Show1 typ, Monad typ) => Show1 (DataDef typ) where
  liftShowsPrec = $(makeLiftShowsPrec ''DataDef)
