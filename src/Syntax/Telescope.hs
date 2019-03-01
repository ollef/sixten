{-# LANGUAGE
  DeriveFoldable,
  DeriveFunctor,
  DeriveTraversable,
  FlexibleContexts,
  GADTs,
  GeneralizedNewtypeDeriving,
  OverloadedStrings,
  Rank2Types,
  TemplateHaskell,
  ViewPatterns
 #-}
module Syntax.Telescope where

import Protolude

import Bound hiding (Var)
import Bound.Scope
import qualified Bound.Var as Bound
import Control.Monad.Morph
import Data.Bifoldable
import Data.Bitraversable
import Data.Deriving
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Functor.Classes
import Data.List(groupBy)
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Syntax.Context

import Effect
import qualified Effect.Context as Context
import Pretty
import Syntax.Annotation
import Syntax.GlobalBind
import Syntax.Name
import Syntax.NameHint
import Util

newtype TeleVar = TeleVar Int
  deriving (Eq, Enum, Hashable, Ord, Show, Num)

unTeleVar :: TeleVar -> Int
unTeleVar (TeleVar i) = i

newtype Telescope expr v = Telescope (Vector (TeleBinding expr v))
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

unTelescope :: Telescope expr v -> Vector (TeleBinding expr v)
unTelescope (Telescope xs) = xs

data TeleBinding expr v = TeleBinding !NameHint !Plicitness !(Scope TeleVar expr v)
  deriving (Eq, Ord, Show, Foldable, Functor, Traversable)

bindingTelescope
  :: (Monad e, Eq v, Hashable v)
  => Vector (v, Binding (e v))
  -> Telescope e v
bindingTelescope vs
  = Telescope
  $ (\(_, Binding h p t _) -> TeleBinding h p $ abstract abstr t)
  <$> vs
  where
    abstr = teleAbstraction $ fst <$> vs

varTelescope
  :: (Monad e, MonadContext (e Var) m)
  => Vector Var
  -> m (Telescope e Var)
varTelescope vs = do
  context <- getContext
  let
    bs = (`Context.lookup` context) <$> vs
  return
    $ Telescope
    $ (\(Binding h p t _) -> TeleBinding h p $ abstract abstr t)
    <$> bs
  where
    abstr = teleAbstraction vs

plicitVarTelescope
  :: (Monad e, MonadContext (e Var) m)
  => Vector (Plicitness, Var)
  -> m (Telescope e Var)
plicitVarTelescope pvs = do
  context <- getContext
  let
    pbs = second (`Context.lookup` context) <$> pvs
  return
    $ Telescope
    $ (\(p, Binding h _ t _) -> TeleBinding h p $ abstract abstr t)
    <$> pbs
  where
    abstr = teleAbstraction $ snd <$> pvs

varTypeTelescope
  :: (Monad e, MonadContext e' m)
  => Vector (Var, e Var)
  -> m (Telescope e Var)
varTypeTelescope vs = do
  context <- getContext
  let
    bs = first (`Context.lookup` context) <$> vs
  return
    $ Telescope
    $ (\(Binding h p _ _, t) -> TeleBinding h p $ abstract abstr t)
    <$> bs
  where
    abstr = teleAbstraction (fst <$> vs)

teleExtendContext
  :: (MonadFresh m, MonadContext (e Var) m, Monad e)
  => Telescope e Var
  -> (Vector Var -> m a)
  -> m a
teleExtendContext tele k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele (pure . fst) vs s
    v <- Context.freeVar
    return (v, binding h p e)
  Context.extends vs $ k $ fst <$> vs

teleMapExtendContext
  :: (MonadFresh m, MonadContext e' m, Monad e)
  => Telescope e Var
  -> (e Var -> m e')
  -> (Vector Var -> m a)
  -> m a
teleMapExtendContext tele f k = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    let e = instantiateTele (pure . fst) vs s
    e' <- Context.extends vs $ f e
    v <- Context.freeVar
    return (v, binding h p e')
  Context.extends vs $ k $ fst <$> vs

mapPlics :: (Plicitness -> Plicitness) -> Telescope e v -> Telescope e v
mapPlics f (Telescope xs) = Telescope $ (\(TeleBinding h a s) -> TeleBinding h (f a) s) <$> xs

bimapTelescope
  :: Bifunctor e
  => (a -> a')
  -> (v -> v')
  -> Telescope (e a) v
  -> Telescope (e a') v'
bimapTelescope f g (Telescope xs)
  = Telescope $ (\(TeleBinding h p s) -> TeleBinding h p (bimapScope f g s)) <$> xs

bifoldMapTelescope
  :: (Bifoldable e, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Telescope (e a) v
  -> m
bifoldMapTelescope f g (Telescope xs)
  = Foldable.fold $ (\(TeleBinding _ _ s) -> bifoldMapScope f g s) <$> xs

bitraverseTelescope
  :: (Bitraversable e, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Telescope (e a) v
  -> f (Telescope (e a') v')
bitraverseTelescope f g (Telescope xs)
  = Telescope <$> traverse (\(TeleBinding h p s) -> TeleBinding h p <$> bitraverseScope f g s) xs

teleLength :: Telescope e v -> Int
teleLength = Vector.length . unTelescope

dropTele
  :: Functor expr
  => Int
  -> Telescope expr v
  -> Telescope expr v
dropTele n
  = Telescope
  . fmap (\(TeleBinding h p s) -> TeleBinding h p $ mapBound (subtract $ TeleVar n) s)
  . Vector.drop n
  . unTelescope

takeTele
  :: Int
  -> Telescope expr v
  -> Telescope expr v
takeTele n = Telescope . Vector.take n . unTelescope

instantiatePrefix
  :: Monad expr
  => Vector (expr v)
  -> Telescope expr v
  -> Telescope expr v
instantiatePrefix es (Telescope tele)
  = Telescope
  $ (\(TeleBinding h p s) -> TeleBinding h p $ toScope $ instantiate f $ F <$> s)
  <$> Vector.drop len tele
  where
    es' = fmap F <$> es
    len = Vector.length es
    f (TeleVar i)
      | i < len = es' Vector.! i
      | otherwise = pure $ B $ TeleVar $! i - len

teleHints :: Telescope expr v -> Vector NameHint
teleHints (Telescope t) = (\(TeleBinding h _ _) -> h) <$> t

addTeleNames :: Telescope expr v -> Vector NameHint -> Telescope expr v
addTeleNames (Telescope t) hs = Telescope $ Vector.imap (\i (TeleBinding h p s) -> TeleBinding (maybe h (h <>) $ hs Vector.!? i) p s) t

telePlics :: Telescope expr v -> Vector Plicitness
telePlics (Telescope t) = (\(TeleBinding _ p _) -> p) <$> t

teleTypes :: Telescope expr v -> Vector (Scope TeleVar expr v)
teleTypes (Telescope t) = (\(TeleBinding _ _ x) -> x) <$> t

quantify
  :: Monad expr
  => (NameHint -> Plicitness
               -> expr (Bound.Var TeleVar v)
               -> Scope1 expr (Bound.Var TeleVar v')
               -> expr (Bound.Var TeleVar v'))
  -> Telescope expr v
  -> Scope TeleVar expr v'
  -> expr v'
quantify pifun (Telescope ps) s =
   Bound.unvar err id <$> Vector.ifoldr
     (\i (TeleBinding h p s') -> pifun h p (fromScope s') . abstract (abstr i))
     (fromScope s)
     ps
  where
    abstr i (B (TeleVar i')) | i == i' = Just ()
    abstr _ _ = Nothing
    err = panic "quantify Telescope"

withTeleHints
  :: Telescope expr v
  -> (Vector Name -> PrettyDoc)
  -> PrettyDoc
withTeleHints = withNameHints . teleHints

prettyTeleVars
  :: Vector Name
  -> Telescope expr v
  -> PrettyDoc
prettyTeleVars ns t = hsep
  [ prettyAnnotation p $ prettyM $ ns Vector.! i
  | (i, p) <- zip [0..] $ Vector.toList $ telePlics t
  ]

prettyTeleVarTypes
  :: (Eq1 expr, Pretty (expr Doc), Monad expr)
  => Vector Name
  -> Telescope expr Doc
  -> PrettyDoc
prettyTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiateTele (pure . fromName) ns
    vlist = Vector.toList v
    grouped =
      [ (n : [n' | (n', _) <- vlist'], p, t)
      | (n, TeleBinding _ p t):vlist' <- groupBy ((==) `on` (fmap PP.layoutCompact . snd)) $ zip [(0 :: Int)..] vlist]
    go (xs, p, t)
      = prettyAnnotationParens p
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

forMTele
  :: Monad m
  => Telescope expr v
  -> (NameHint -> Plicitness -> Scope TeleVar expr v -> m v')
  -> m (Vector v')
forMTele (Telescope t) f = forM t $ \(TeleBinding h d s) -> f h d s

forTeleWithPrefixM
  :: Monad m
  => Telescope expr v
  -> (NameHint -> Plicitness -> Scope TeleVar expr v -> Vector v' -> m v')
  -> m (Vector v')
forTeleWithPrefixM (Telescope t) f = mapWithPrefixM (\(TeleBinding h d s) -> f h d s) t

forTele
  :: Telescope expr v
  -> (NameHint -> Plicitness -> Scope TeleVar expr v -> v')
  -> Vector v'
forTele (Telescope t) f = (\(TeleBinding h d s) -> f h d s) <$> t

iforMTele
  :: Monad m
  => Telescope expr v
  -> (Int -> NameHint -> Plicitness -> Scope TeleVar expr v -> m v')
  -> m (Vector v')
iforMTele (Telescope t) f = flip Vector.imapM t $ \i (TeleBinding h d s) -> f i h d s

iforTeleWithPrefixM
  :: Monad m
  => Telescope expr v
  -> (Int -> NameHint -> Plicitness -> Scope TeleVar expr v -> Vector v' -> m v')
  -> m (Vector v')
iforTeleWithPrefixM (Telescope t) f = mapWithPrefixM (\(i, TeleBinding h d s) -> f i h d s) $ Vector.indexed t

iforTele
  :: Telescope expr v
  -> (Int -> NameHint -> Plicitness -> Scope TeleVar expr v -> v')
  -> Vector v'
iforTele (Telescope t) f = (\(i, TeleBinding h d s) -> f i h d s) <$> Vector.indexed t

instantiateTele
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope TeleVar f a
  -> f a
instantiateTele f vs
  = instantiate (f . fromMaybe (panic "instantiateTele") . (vs Vector.!?) . unTeleVar)

teleAbstraction :: (Eq a, Hashable a) => Vector a -> a -> Maybe TeleVar
teleAbstraction vs = fmap TeleVar . hashedElemIndex vs

-- | View consecutive bindings at the same time
bindingsViewM
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, Plicitness, expr v', Scope1 expr' v'))
  -> expr' v
  -> Maybe (Telescope expr v, Scope TeleVar expr' v)
bindingsViewM f expr@(f -> Just _) = Just $ bindingsView f expr
bindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
bindingsView
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, Plicitness, expr v', Scope1 expr' v'))
  -> expr' v
  -> (Telescope expr v, Scope TeleVar expr' v)
bindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (TeleBinding n p $ toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ Util.instantiate1 (return $ B x) s
    go _ e = (Telescope mempty, toScope e)

transverseTelescope
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> Telescope expr v
  -> f (Telescope expr' v)
transverseTelescope f (Telescope xs) = Telescope <$> traverse (transverseTeleBinding f) xs

transverseTeleBinding
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> TeleBinding expr v
  -> f (TeleBinding expr' v)
transverseTeleBinding f (TeleBinding h p s) = TeleBinding h p <$> transverseScope f s

-------------------------------------------------------------------------------
-- Instances
instance (v ~ Doc, Eq1 expr, Pretty (expr v), Monad expr)
  => Pretty (Telescope expr v) where
  prettyM tele = withTeleHints tele $ \ns -> prettyTeleVarTypes ns tele

instance Bound Telescope where
  Telescope tele >>>= f
    = Telescope $ (\(TeleBinding h p s) -> TeleBinding h p $ s >>>= f) <$> tele

instance GBound Telescope where
  gbound f (Telescope tele)
    = Telescope $ (\(TeleBinding h p s) -> TeleBinding h p $ gbound f s) <$> tele

instance MFunctor Telescope where
  hoist f (Telescope xs)
    = Telescope $ (\(TeleBinding h p s) -> TeleBinding h p $ hoist f s) <$> xs

$(return mempty)

instance (Eq1 expr, Monad expr) => Eq1 (Telescope expr) where
  liftEq = $(makeLiftEq ''Telescope)

instance (Ord1 expr, Monad expr) => Ord1 (Telescope expr) where
  liftCompare = $(makeLiftCompare ''Telescope)

instance (Show1 expr, Monad expr) => Show1 (Telescope expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Telescope)

instance (Eq1 expr, Monad expr) => Eq1 (TeleBinding expr) where
  liftEq = $(makeLiftEq ''TeleBinding)

instance (Ord1 expr, Monad expr) => Ord1 (TeleBinding expr) where
  liftCompare = $(makeLiftCompare ''TeleBinding)

instance (Show1 expr, Monad expr) => Show1 (TeleBinding expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''TeleBinding)
