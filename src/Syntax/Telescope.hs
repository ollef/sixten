{-# LANGUAGE
  DeriveFoldable,
  DeriveFunctor,
  DeriveTraversable,
  FlexibleContexts,
  GADTs,
  GeneralizedNewtypeDeriving,
  KindSignatures,
  OverloadedStrings,
  Rank2Types,
  StandaloneDeriving,
  ViewPatterns
 #-}
module Syntax.Telescope where

import Bound
import Bound.Scope
import qualified Bound.Scope.Simple as Simple
import Bound.Var
import Data.Bifunctor
import Data.Hashable
import Data.List as List
import Data.Monoid
import Data.String
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Annotation
import Syntax.Hint
import Syntax.Name
import Syntax.Pretty
import Util

newtype Tele = Tele Int
  deriving (Eq, Enum, Hashable, Ord, Show, Num)

unTele :: Tele -> Int
unTele (Tele i) = i

newtype Telescope scope anno (expr :: * -> *) v = Telescope
  { unTelescope :: Vector (NameHint, anno, scope Tele expr v)
  } deriving (Monoid)

deriving instance (Eq anno, Eq (scope Tele expr v)) => Eq (Telescope scope anno expr v)
deriving instance (Ord anno, Ord (scope Tele expr v)) => Ord (Telescope scope anno expr v)
deriving instance (Show anno, Show (scope Tele expr v)) => Show (Telescope scope anno expr v)
deriving instance Foldable (scope Tele expr) => Foldable (Telescope scope anno expr)
deriving instance Functor (scope Tele expr) => Functor (Telescope scope anno expr)
deriving instance Traversable (scope Tele expr) => Traversable (Telescope scope anno expr)

mapAnnotations :: (a -> a') -> Telescope s a e v -> Telescope s a' e v
mapAnnotations f (Telescope xs) = Telescope $ (\(h, a, s) -> (h, f a, s)) <$> xs

teleLength :: Telescope s a e v -> Int
teleLength = Vector.length . unTelescope

dropTele
  :: Functor expr
  => Int
  -> Telescope Scope a expr v
  -> Telescope Scope a expr v
dropTele n
  = Telescope
  . fmap (\(h, p, s) -> (h, p, mapBound (subtract $ Tele n) s))
  . Vector.drop n
  . unTelescope

instantiatePrefix
  :: Monad expr
  => Vector (expr v)
  -> Telescope Scope a expr v
  -> Telescope Scope a expr v
instantiatePrefix es (Telescope tele)
  = Telescope
  $ (\(h, p, s) -> (h, p, toScope $ instantiate f $ F <$> s))
  <$> Vector.drop len tele
  where
    es' = fmap F <$> es
    len = Vector.length es
    f (Tele i)
      | i < len = es' Vector.! i
      | otherwise = pure $ B $ Tele $! i - len

teleNames :: Telescope s a expr v -> Vector NameHint
teleNames (Telescope t) = (\(h, _, _) -> h) <$> t

teleAnnotations :: Telescope s a expr v -> Vector a
teleAnnotations (Telescope t) = (\(_, a, _) -> a) <$> t

teleNamedAnnotations :: Telescope s a e v -> Vector (NameHint, a)
teleNamedAnnotations (Telescope tele) = (\(h, a, _) -> (h, a)) <$> tele

teleTypes :: Telescope s a expr v -> Vector (s Tele expr v)
teleTypes (Telescope t) = (\(_, _, x) -> x) <$> t

quantify
  :: (Eq v', Monad expr)
  => (NameHint -> a
               -> expr (Var Tele v)
               -> Scope () expr (Var Tele v')
               -> expr (Var Tele v'))
  -> Scope Tele expr v'
  -> Telescope Scope a expr v
  -> expr v'
quantify pifun s (Telescope ps) =
   unvar err id <$> Vector.ifoldr
     (\i (h, p, s') -> pifun h p (fromScope s') . abstract1 (B $ Tele i))
     (fromScope s)
     ps
  where
    err = error "quantify Telescope"

instance Bound (s Tele) => Bound (Telescope s a) where
  Telescope t >>>= f = Telescope $ second (>>>= f) <$> t

exposeTelescope
  :: Applicative expr
  => (forall w. expr w -> expr (Var e w))
  -> Telescope Scope a expr v
  -> Telescope Scope a expr (Var e v)
exposeTelescope f (Telescope t) = Telescope $ second (exposeScope f) <$> t

withTeleHints
  :: Telescope s a expr v
  -> (Vector Name -> PrettyM p)
  -> PrettyM p
withTeleHints = withNameHints . teleNames

prettyTeleVars
  :: Vector Name
  -> Telescope s Annotation expr v
  -> PrettyM Doc
prettyTeleVars ns t = hsep
  [ prettyAnnotation a $ prettyM $ ns Vector.! i
  | (i, a) <- zip [0..] $ Vector.toList $ teleAnnotations t
  ]

prettyTeleVarTypes
  :: (Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
  => Vector Name
  -> Telescope Scope Annotation expr v
  -> PrettyM Doc
prettyTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiate $ pure . fromText . (ns Vector.!) . unTele
    vlist = Vector.toList v
    grouped = [ (n : [n' | (Hint n', _) <- vlist'], a, t)
              | (Hint n, (_, a, t)):vlist' <- List.group $ zip (map Hint [(0 :: Int)..]) vlist]
    go (xs, a, t)
      = prettyAnnotationParens a
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

instance (a ~ Annotation, s ~ Scope, Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
  => Pretty (Telescope s a expr v) where
  prettyM tele = withTeleHints tele $ \ns -> prettyTeleVarTypes ns tele

prettySimpleTeleVarTypes
  :: (Eq1 expr, Eq v, Pretty (expr v), Functor expr, IsString v, Eq a)
  => Vector Name
  -> Telescope Simple.Scope a expr v
  -> PrettyM Doc
prettySimpleTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiateVar $ fromText . (ns Vector.!) . unTele
    vlist = Vector.toList v
    grouped = [ (n : [n' | (Hint n', _) <- vlist'], a, t)
              | (Hint n, (_, a, t)):vlist' <- List.group $ zip (map Hint [(0 :: Int)..]) vlist]
    go (xs, _, t)
      = parens `above` annoPrec
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

forMTele
  :: Monad m
  => Telescope s a expr v
  -> (NameHint -> a -> s Tele expr v -> m v')
  -> m (Vector v')
forMTele (Telescope t) f = forM t $ \(h, d, s) -> f h d s

forTele
  :: Telescope s a expr v
  -> (NameHint -> a -> s Tele expr v -> v')
  -> Vector v'
forTele (Telescope t) f = (\(h, d, s) -> f h d s) <$> t

iforMTele
  :: Monad m
  => Telescope s a expr v
  -> (Int -> NameHint -> a -> s Tele expr v -> m v')
  -> m (Vector v')
iforMTele (Telescope t) f = flip Vector.imapM t $ \i (h, d, s) -> f i h d s

instantiateTele
  :: Monad f
  => Vector (f a)
  -> Scope Tele f a
  -> f a
instantiateTele vs = instantiate ((vs Vector.!) . unTele)

instantiateTeleVars :: Functor f => Vector a -> Simple.Scope Tele f a -> f a
instantiateTeleVars vs = instantiateVar ((vs Vector.!) . unTele)

instantiateSimpleTeleVars
  :: Functor f
  => Vector a
  -> Simple.Scope Tele f a
  -> f a
instantiateSimpleTeleVars vs = instantiateVar ((vs Vector.!) . unTele)

teleAbstraction :: Eq a => Vector a -> a -> Maybe Tele
teleAbstraction vs = fmap Tele . (`Vector.elemIndex` vs)

-- | View consecutive bindings at the same time
bindingsViewM
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Scope1 expr' v'))
  -> expr' v
  -> Maybe (Telescope Scope a expr v, Scope Tele expr' v)
bindingsViewM f expr@(f -> Just _) = Just $ bindingsView f expr
bindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
bindingsView
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Scope1 expr' v'))
  -> expr' v
  -> (Telescope Scope a expr v, Scope Tele expr' v)
bindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (n, p, toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ instantiate1 (return $ B x) s
    go _ e = (mempty, toScope e)

-- | View consecutive bindings at the same time
simpleBindingsViewM
  :: (Functor expr, Functor expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Simple.Scope () expr' v'))
  -> expr' v
  -> Maybe (Telescope Simple.Scope a expr v, Simple.Scope Tele expr' v)
simpleBindingsViewM f expr@(f -> Just _) = Just $ simpleBindingsView f expr
simpleBindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
simpleBindingsView
  :: (Functor expr, Functor expr')
  => (forall v'. expr' v' -> Maybe (NameHint, a, expr v', Simple.Scope () expr' v'))
  -> expr' v
  -> (Telescope Simple.Scope a expr v, Simple.Scope Tele expr' v)
simpleBindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (n, p, Simple.toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ instantiate1Var (B x) s
    go _ e = (mempty, Simple.toScope e)
