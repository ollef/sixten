{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, Rank2Types, ViewPatterns, OverloadedStrings #-}
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

newtype Telescope expr v = Telescope
  { unTelescope :: Vector (NameHint, Annotation, Scope Tele expr v)
  } deriving (Eq, Foldable, Functor, Monoid, Ord, Show, Traversable)

newtype SimpleTelescope expr v = SimpleTelescope
  { unSimpleTelescope :: Vector (NameHint, Simple.Scope Tele expr v)
  } deriving (Eq, Foldable, Functor, Monoid, Ord, Show, Traversable)

mapAnnotations :: (Annotation -> Annotation) -> Telescope e v -> Telescope e v
mapAnnotations f (Telescope xs) = Telescope $ (\(h, a, s) -> (h, f a, s)) <$> xs

teleLength :: Telescope expr v -> Int
teleLength = Vector.length . unTelescope

dropTele :: Functor expr => Int -> Telescope expr v -> Telescope expr v
dropTele n
  = Telescope
  . fmap (\(h, p, s) -> (h, p, mapBound (subtract $ Tele n) s))
  . Vector.drop n
  . unTelescope

instantiatePrefix
  :: Monad expr
  => Vector (expr v)
  -> Telescope expr v
  -> Telescope expr v
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

teleNames :: Telescope expr v -> Vector NameHint
teleNames (Telescope t) = (\(h, _, _) -> h) <$> t

simpleTeleNames :: SimpleTelescope expr v -> Vector NameHint
simpleTeleNames (SimpleTelescope t) = fst <$> t

teleAnnotations :: Telescope expr v -> Vector Annotation
teleAnnotations (Telescope t) = (\(_, a, _) -> a) <$> t

teleTypes :: Telescope expr v -> Vector (Scope Tele expr v)
teleTypes (Telescope t) = (\(_, _, x) -> x) <$> t

quantify :: (Eq b, Monad expr)
         => (NameHint -> Annotation
                      -> expr (Var Tele a)
                      -> Scope () expr (Var Tele b)
                      -> expr (Var Tele b))
         -> Scope Tele expr b
         -> Telescope expr a
         -> expr b
quantify pifun s (Telescope ps) =
   unvar err id <$> Vector.ifoldr
     (\i (h, p, s') -> pifun h p (fromScope s') . abstract1 (B $ Tele i))
     (fromScope s)
     ps
  where
    err = error "quantify Telescope"

instance Bound Telescope where
  Telescope t >>>= f = Telescope $ second (>>>= f) <$> t

instance Bound SimpleTelescope where
  SimpleTelescope t >>>= f = SimpleTelescope $ second (>>>= f) <$> t

exposeTelescope :: Applicative expr
                => (forall v. expr v -> expr (Var e v))
                -> Telescope expr a
                -> Telescope expr (Var e a)
exposeTelescope f (Telescope t) = Telescope $ second (exposeScope f) <$> t

withTeleHints :: Telescope expr v -> (Vector Name -> PrettyM a) -> PrettyM a
withTeleHints = withNameHints . teleNames

withSimpleTeleHints :: SimpleTelescope expr v -> (Vector Name -> PrettyM a) -> PrettyM a
withSimpleTeleHints = withNameHints . simpleTeleNames

prettyTeleVars :: Vector Name -> Telescope expr v -> PrettyM Doc
prettyTeleVars ns t = hsep
  [ prettyAnnotation a $ prettyM $ ns Vector.! i
  | (i, a) <- zip [0..] $ Vector.toList $ teleAnnotations t
  ]

prettyTeleVarTypes :: (Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
                   => Vector Name -> Telescope expr v -> PrettyM Doc
prettyTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiate $ pure . fromText . (ns Vector.!) . unTele
    vlist = Vector.toList v
    grouped = [ (n : [n' | (Hint n', _) <- vlist'], a, t)
              | (Hint n, (_, a, t)):vlist' <- List.group $ zip (map Hint [(0 :: Int)..]) vlist]
    go (xs, a, t)
      = prettyAnnotationParens a
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

instance (Eq1 expr, Eq v, Pretty (expr v), Monad expr, IsString v)
  => Pretty (Telescope expr v) where
  prettyM tele = withTeleHints tele $ \ns -> prettyTeleVarTypes ns tele

prettySimpleTeleVarTypes
  :: (Eq1 expr, Eq v, Pretty (expr v), Functor expr, IsString v)
  => Vector Name -> SimpleTelescope expr v -> PrettyM Doc
prettySimpleTeleVarTypes ns (SimpleTelescope v) = hcat $ map go grouped
  where
    inst = instantiateVar $ fromText . (ns Vector.!) . unTele
    vlist = Vector.toList v
    grouped = [ (n : [n' | (Hint n', _) <- vlist'], t)
              | (Hint n, (_, t)):vlist' <- List.group $ zip (map Hint [(0 :: Int)..]) vlist]
    go (xs, t)
      = parens `above` annoPrec
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> ":" <+> prettyM (inst t)

forMTele
  :: Monad m
  => Telescope expr a
  -> (NameHint -> Annotation -> Scope Tele expr a -> m b)
  -> m (Vector b)
forMTele (Telescope t) f = forM t $ \(h, d, s) -> f h d s

forMSimpleTele
  :: Monad m
  => SimpleTelescope expr a
  -> (NameHint -> Simple.Scope Tele expr a -> m b)
  -> m (Vector b)
forMSimpleTele (SimpleTelescope t) f = forM t $ uncurry f


forTele
  :: Telescope expr a
  -> (NameHint -> Annotation -> Scope Tele expr a -> b)
  -> Vector b
forTele (Telescope t) f = (\(h, d, s) -> f h d s) <$> t

iforMTele :: Monad m
         => Telescope expr a
         -> (Int -> NameHint -> Annotation -> Scope Tele expr a -> m b)
         -> m (Vector b)
iforMTele (Telescope t) f = flip Vector.imapM t $ \i (h, d, s) -> f i h d s

instantiateTele :: Monad f => Vector (f a) -> Scope Tele f a -> f a
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
  => (forall v'. expr' v' -> Maybe (NameHint, Annotation, expr v', Scope1 expr' v'))
  -> expr' v
  -> Maybe (Telescope expr v, Scope Tele expr' v)
bindingsViewM f expr@(f -> Just _) = Just $ bindingsView f expr
bindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
bindingsView
  :: (Monad expr, Monad expr')
  => (forall v'. expr' v' -> Maybe (NameHint, Annotation, expr v', Scope1 expr' v'))
  -> expr' v
  -> (Telescope expr v, Scope Tele expr' v)
bindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (n, p, toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ instantiate1 (return $ B x) s
    go _ e = (mempty, toScope e)

-- | View consecutive bindings at the same time
simpleBindingsViewM
  :: (Functor expr, Functor expr')
  => (forall v'. expr' v' -> Maybe (NameHint, expr v', Simple.Scope () expr' v'))
  -> expr' v
  -> Maybe (SimpleTelescope expr v, Simple.Scope Tele expr' v)
simpleBindingsViewM f expr@(f -> Just _) = Just $ simpleBindingsView f expr
simpleBindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
simpleBindingsView
  :: (Functor expr, Functor expr')
  => (forall v'. expr' v' -> Maybe (NameHint, expr v', Simple.Scope () expr' v'))
  -> expr' v
  -> (SimpleTelescope expr v, Simple.Scope Tele expr' v)
simpleBindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, e, s)) = (SimpleTelescope $ pure (n, Simple.toScope e) <> ns, s')
      where
        (SimpleTelescope ns, s') = (go $! x + 1) $ instantiate1Var (B x) s
    go _ e = (mempty, Simple.toScope e)
