{-# LANGUAGE
  DeriveFoldable,
  DeriveFunctor,
  DeriveTraversable,
  FlexibleContexts,
  FlexibleInstances,
  GADTs,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  OverloadedStrings,
  Rank2Types,
  StandaloneDeriving,
  TemplateHaskell,
  UndecidableInstances,
  ViewPatterns
 #-}
module Syntax.Telescope where

import Bound.Var
import Control.Monad.Morph
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Deriving
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Functor.Classes
import Data.Hashable
import Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax.Binds
import Syntax.GlobalBind
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

newtype Telescope anno expr v = Telescope (Vector (TeleArg anno expr v))
  deriving (Show, Foldable, Functor, Traversable)

deriving instance (Eq anno, Eq1 expr, Binds expr expr, Eq v) => Eq (Telescope anno expr v)
deriving instance (Ord anno, Ord1 expr, Binds expr expr, Ord v) => Ord (Telescope anno expr v)

data TeleArg anno expr v = TeleArg !NameHint !anno !(Scope expr TeleVar expr v)
  deriving (Show, Foldable, Functor, Traversable)

deriving instance (Eq anno, Eq1 expr, Binds expr expr, Eq v) => Eq (TeleArg anno expr v)
deriving instance (Ord anno, Ord1 expr, Binds expr expr, Ord v) => Ord (TeleArg anno expr v)

unTelescope :: Telescope anno expr v -> Vector (TeleArg anno expr v)
unTelescope (Telescope xs) = xs

mapAnnotations :: (a -> a') -> Telescope a e v -> Telescope a' e v
mapAnnotations f (Telescope xs) = Telescope $ (\(TeleArg h a s) -> (TeleArg h (f a) s)) <$> xs

bimapTelescope
  :: Bifunctor e
  => (a -> a')
  -> (v -> v')
  -> Telescope p (e a) v
  -> Telescope p (e a') v'
bimapTelescope f g (Telescope xs)
  = Telescope $ (\(TeleArg h p s) -> TeleArg h p (bimapScope' f g s)) <$> xs

bifoldMapTelescope
  :: (Bifoldable e, Monoid m)
  => (a -> m)
  -> (v -> m)
  -> Telescope p (e a) v
  -> m
bifoldMapTelescope f g (Telescope xs)
  = Foldable.fold $ (\(TeleArg _ _ s) -> bifoldMapScope' f g s) <$> xs

bitraverseTelescope
  :: (Bitraversable e, Applicative f)
  => (a -> f a')
  -> (v -> f v')
  -> Telescope p (e a) v
  -> f (Telescope p (e a') v')
bitraverseTelescope f g (Telescope xs)
  = Telescope <$> traverse (\(TeleArg h p s) -> TeleArg h p <$> bitraverseScope' f g s) xs

teleLength :: Telescope a e v -> Int
teleLength = Vector.length . unTelescope

dropTele
  :: Functor expr
  => Int
  -> Telescope a expr v
  -> Telescope a expr v
dropTele n
  = Telescope
  . fmap (\(TeleArg h p s) -> (TeleArg h p $ mapBound (subtract $ TeleVar n) s))
  . Vector.drop n
  . unTelescope

takeTele
  :: Int
  -> Telescope a expr v
  -> Telescope a expr v
takeTele n = Telescope . Vector.take n . unTelescope

instantiatePrefix
  :: Binds expr expr
  => Vector (expr v)
  -> Telescope a expr v
  -> Telescope a expr v
instantiatePrefix es (Telescope tele)
  = Telescope
  $ (\(TeleArg h p s) -> TeleArg h p $ toScope $ instantiate f $ F <$> s)
  <$> Vector.drop len tele
  where
    es' = fmap F <$> es
    len = Vector.length es
    f (TeleVar i)
      | i < len = es' Vector.! i
      | otherwise = pure $ B $ TeleVar $! i - len

teleNames :: Telescope a expr v -> Vector NameHint
teleNames (Telescope t) = (\(TeleArg h _ _) -> h) <$> t

addTeleNames :: Telescope a expr v -> Vector NameHint -> Telescope a expr v
addTeleNames (Telescope t) hs = Telescope $ Vector.imap (\i (TeleArg h a s) -> TeleArg (maybe h (h <>) $ hs Vector.!? i) a s) t

teleAnnotations :: Telescope a expr v -> Vector a
teleAnnotations (Telescope t) = (\(TeleArg _ a _) -> a) <$> t

teleTypes :: Telescope a expr v -> Vector (Scope expr TeleVar expr v)
teleTypes (Telescope t) = (\(TeleArg _ _ x) -> x) <$> t

quantify
  :: Monad expr
  => (NameHint -> a
               -> expr (Var TeleVar v)
               -> Scope1 expr (Var TeleVar v')
               -> expr (Var TeleVar v'))
  -> Telescope a expr v
  -> Scope expr TeleVar expr v'
  -> expr v'
quantify pifun (Telescope ps) s =
   unvar err id <$> Vector.ifoldr
     (\i (TeleArg h p s') -> pifun h p (fromScope s') . abstract (abstr i))
     (fromScope s)
     ps
  where
    abstr i (B (TeleVar i')) | i == i' = Just ()
    abstr _ _ = Nothing
    err = error "quantify Telescope"

withTeleHints
  :: Telescope a expr v
  -> (Vector Name -> PrettyM p)
  -> PrettyM p
withTeleHints = withNameHints . teleNames

prettyTeleVars
  :: PrettyAnnotation a
  => Vector Name
  -> Telescope a expr v
  -> PrettyM Doc
prettyTeleVars ns t = hsep
  [ prettyAnnotation a $ prettyM $ ns Vector.! i
  | (i, a) <- zip [0..] $ Vector.toList $ teleAnnotations t
  ]

prettyTeleVarTypes
  :: (Eq1 expr, Pretty (expr Doc), Monad expr, PrettyAnnotation a)
  => Vector Name
  -> Telescope a expr Doc
  -> PrettyM Doc
prettyTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiateTele (pure . fromName) ns
    vlist = Vector.toList v
    grouped =
      [ (n : [n' | (n', _) <- vlist'], a, t)
      | (n, TeleArg _ a t):vlist' <- List.groupBy ((==) `on` (fmap PP.layoutCompact . snd)) $ zip [(0 :: Int)..] vlist]
    go (xs, a, t)
      = prettyAnnotationParens a
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

forMTele
  :: Monad m
  => Telescope a expr v
  -> (NameHint -> a -> Scope expr TeleVar expr v -> m v')
  -> m (Vector v')
forMTele (Telescope t) f = forM t $ \(TeleArg h d s) -> f h d s

forTeleWithPrefixM
  :: Monad m
  => Telescope a expr v
  -> (NameHint -> a -> Scope expr TeleVar expr v -> Vector v' -> m v')
  -> m (Vector v')
forTeleWithPrefixM (Telescope t) f = mapWithPrefixM (\(TeleArg h d s) -> f h d s) t

forTele
  :: Telescope a expr v
  -> (NameHint -> a -> Scope expr TeleVar expr v -> v')
  -> Vector v'
forTele (Telescope t) f = (\(TeleArg h d s) -> f h d s) <$> t

iforMTele
  :: Monad m
  => Telescope a expr v
  -> (Int -> NameHint -> a -> Scope expr TeleVar expr v -> m v')
  -> m (Vector v')
iforMTele (Telescope t) f = flip Vector.imapM t $ \i (TeleArg h d s) -> f i h d s

iforTeleWithPrefixM
  :: Monad m
  => Telescope a expr v
  -> (Int -> NameHint -> a -> Scope expr TeleVar expr v -> Vector v' -> m v')
  -> m (Vector v')
iforTeleWithPrefixM (Telescope t) f = mapWithPrefixM (\(i, TeleArg h d s) -> f i h d s) $ Vector.indexed t

iforTele
  :: Telescope a expr v
  -> (Int -> NameHint -> a -> Scope expr TeleVar expr v -> v')
  -> Vector v'
iforTele (Telescope t) f = (\(i, TeleArg h d s) -> f i h d s) <$> Vector.indexed t

instantiateTele
  :: Monad f
  => (v -> f a)
  -> Vector v
  -> Scope f TeleVar f a
  -> f a
instantiateTele f vs
  = instantiate (f . fromMaybe (error "instantiateTele") . (vs Vector.!?) . unTeleVar)

teleAbstraction :: (Eq a, Hashable a) => Vector a -> a -> Maybe TeleVar
teleAbstraction vs = fmap TeleVar . hashedElemIndex vs

-- | View consecutive bindings at the same time
bindingsViewM
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Scope1 expr' v'))
  -> expr' v
  -> Maybe (Telescope a expr v, Scope expr TeleVar expr' v)
bindingsViewM f expr@(f -> Just _) = Just $ bindingsView f expr
bindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
bindingsView
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Scope1 expr' v'))
  -> expr' v
  -> (Telescope a expr v, Scope expr' TeleVar expr' v)
bindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (TeleArg n p $ toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ Util.instantiate1 (return $ B x) s
    go _ e = (Telescope mempty, toScope e)

transverseTelescope
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> Telescope a expr v
  -> f (Telescope a expr' v)
transverseTelescope f (Telescope xs) = Telescope <$> traverse (transverseTeleArg f) xs

transverseTeleArg
  :: (Monad f, Traversable expr)
  => (forall r. expr r -> f (expr' r))
  -> TeleArg a expr v
  -> f (TeleArg a expr' v)
transverseTeleArg f (TeleArg h a s) = TeleArg h a <$> transverseScope f s

-------------------------------------------------------------------------------
-- Instances
instance (a ~ Plicitness, v ~ Doc, Eq1 expr, Pretty (expr v), Monad expr)
  => Pretty (Telescope a expr v) where
  prettyM tele = withTeleHints tele $ \ns -> prettyTeleVarTypes ns tele

instance BindsGlobal expr (Telescope a expr) where
  bind f (Telescope tele)
    = Telescope $ (\(TeleArg h a s) -> TeleArg h a $ bound f g s) <$> tele

instance MFunctor (Telescope a) where
  hoist f (Telescope xs)
    = Telescope $ (\(TeleArg h p s) -> TeleArg h p $ hoist f s) <$> xs

$(return mempty)

instance (Eq anno, Eq1 expr, Monad expr) => Eq1 (Telescope anno expr) where
  liftEq = $(makeLiftEq ''Telescope)

instance (Ord anno, Ord1 expr, Monad expr) => Ord1 (Telescope anno expr) where
  liftCompare = $(makeLiftCompare ''Telescope)

instance (Show anno, Show1 expr, Monad expr) => Show1 (Telescope anno expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Telescope)

instance (Eq anno, Eq1 expr, Monad expr) => Eq1 (TeleArg anno expr) where
  liftEq = $(makeLiftEq ''TeleArg)

instance (Ord anno, Ord1 expr, Monad expr) => Ord1 (TeleArg anno expr) where
  liftCompare = $(makeLiftCompare ''TeleArg)

instance (Show anno, Show1 expr, Monad expr) => Show1 (TeleArg anno expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''TeleArg)
