{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings, RankNTypes #-}
module Syntax.Data where

import Protolude

import Bound hiding (Var)
import Bound.Scope
import Control.Monad.Morph
import Data.Bitraversable
import Data.Functor.Classes
import Data.Vector(Vector)

import Effect.Context as Context
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.Telescope
import Util

data DataDef typ v = DataDef
  { dataParams :: Telescope typ v
  , dataConstructors :: [ConstrDef (Telescope typ v, Scope TeleVar typ v)]
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

dataDef
  :: (Monad typ, MonadContext (typ Var) m)
  => Vector Var
  -> [ConstrDef (Vector Var, typ Var)]
  -> m (DataDef typ Var)
dataDef vs cs = do
  let abstr = abstract . teleAbstraction vs
  cs' <- forM cs $ \(ConstrDef c (vs', typ)) -> do
    tele <- varTelescope vs'
    return $ ConstrDef c (tele, abstract (teleAbstraction vs') typ)
  tele <- varTelescope vs
  return $ DataDef tele cs'

plicitDataDef
  :: (Monad typ, MonadContext (typ Var) m)
  => Vector (Plicitness, Var)
  -> [ConstrDef (Vector (Plicitness, Var), typ Var)]
  -> m (DataDef typ Var)
plicitDataDef pvs cs = do
  cs' <- forM cs $ \(ConstrDef c (pvs', typ)) -> do
    tele <- plicitVarTelescope pvs'
    return $ ConstrDef c (tele, abstract (teleAbstraction $ snd <$> pvs') typ)
  tele <- plicitVarTelescope pvs
  return $ DataDef tele cs'

instance Bound DataDef where
  DataDef ps cs >>>= f = DataDef (ps >>>= f) $ fmap (bimap (>>>= f) (>>>= f)) <$> cs

instance GBound DataDef where
  gbound f (DataDef ps cs) = DataDef (gbound f ps) $ fmap (bimap (gbound f) (gbound f)) <$> cs

instance MFunctor DataDef where
  hoist f (DataDef ps cs) = DataDef (hoist f ps) $ fmap (bimap (hoist f) (hoistScope f)) <$> cs

bimapDataDef
  :: Bifunctor typ
  => (a -> a')
  -> (b -> b')
  -> DataDef (typ a) b
  -> DataDef (typ a') b'
bimapDataDef f g (DataDef ps cs)
  = DataDef (bimapTelescope f g ps)
  $ fmap (bimap (bimapTelescope f g) (bimapScope f g)) <$> cs

bitraverseDataDef
  :: (Bitraversable typ, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> DataDef (typ a) b
  -> f (DataDef (typ a') b')
bitraverseDataDef f g (DataDef ps cs)
  = DataDef
  <$> bitraverseTelescope f g ps
  <*> traverse (traverse $ bitraverse (bitraverseTelescope f g) (bitraverseScope f g)) cs

transverseDataDef
  :: (Traversable typ, Monad f)
  => (forall r. typ r -> f (typ' r))
  -> DataDef typ a
  -> f (DataDef typ' a)
transverseDataDef f (DataDef ps cs)
  = DataDef
  <$> transverseTelescope f ps
  <*> traverse (traverse $ bitraverse (transverseTelescope f) (transverseScope f)) cs

constrNames :: DataDef typ v -> [Constr]
constrNames = map constrName . dataConstructors

data ConstrDef typ = ConstrDef
  { constrName :: Constr
  , constrType :: typ
  } deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance (v ~ Doc, Pretty (typ v), Monad typ, Eq1 typ) => PrettyNamed (DataDef typ v) where
  prettyNamed name (DataDef ps cs) = withTeleHints ps $ \ns -> do
    let inst = instantiateTele (pure . fromName) ns
    "type" <+> name <+> prettyTeleVarTypes ns ps <+> "where" <$$>
      indent 2 (vcat $ map (prettyM . fmap inst . snd) cs)

instance Pretty typ => Pretty (ConstrDef typ) where
  prettyM (ConstrDef n t) = prettyM n <+> ":" <+> prettyM t
