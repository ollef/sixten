{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, Rank2Types, ViewPatterns #-}
module Syntax.Telescope where

import Bound
import Bound.Scope
import Bound.Var
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
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

newtype Tele = Tele
  { unTele :: Int
  } deriving (Eq, Ord, Show, Num)

newtype Telescope d expr v = Telescope
  { unTelescope :: Vector (NameHint, d, Scope Tele expr v)
  } deriving (Eq, Foldable, Functor, Monoid, Ord, Show, Traversable)

teleLength :: Telescope d expr v -> Int
teleLength = Vector.length . unTelescope

teleNames :: Telescope d expr v -> Vector NameHint
teleNames (Telescope t) = (\(h, _, _) -> h) <$> t

teleAnnotations :: Telescope d expr v -> Vector d
teleAnnotations (Telescope t) = (\(_, a, _) -> a) <$> t

teleTypes :: Telescope d expr v -> Vector (Scope Tele expr v)
teleTypes (Telescope t) = (\(_, _, x) -> x) <$> t

quantify :: (Eq b, Monad expr)
         => (NameHint -> d
                      -> expr (Var Tele a)
                      -> Scope () expr (Var Tele b)
                      -> expr (Var Tele b))
         -> Scope Tele expr b
         -> Telescope d expr a
         -> expr b
quantify pifun s (Telescope ps) =
   unvar err id <$> Vector.ifoldr
     (\i (h, p, s') -> pifun h p (fromScope s') . abstract1 (B $ Tele i))
     (fromScope s)
     ps
  where
    err = error "quantify Telescope"

instance Bound (Telescope d) where
  Telescope t >>>= f = Telescope $ second (>>>= f) <$> t

exposeTelescope :: Applicative expr
                => (forall v. expr v -> expr (Var e v))
                -> Telescope d expr a
                -> Telescope d expr (Var e a)
exposeTelescope f (Telescope t) = Telescope $ second (exposeScope f) <$> t

trimapTelescope :: Bifunctor expr
                => (d -> d') -> (x -> x') -> (y -> y')
                -> Telescope d (expr x) y
                -> Telescope d' (expr x') y'
trimapTelescope e f g (Telescope t) = Telescope $ bimap e (bimapScope f g) <$> t

trifoldMapTelescope :: (Bifoldable expr, Monoid m)
                  => (d -> m) -> (x -> m) -> (y -> m)
                  -> Telescope d (expr x) y
                  -> m
trifoldMapTelescope e f g (Telescope t) = foldMap (bifoldMap e (bifoldMapScope f g)) t

tritraverseTelescope :: (Applicative f, Bitraversable expr)
                    => (d -> f d') -> (x -> f x') -> (y -> f y')
                    -> Telescope d (expr x) y
                    -> f (Telescope d' (expr x') y')
tritraverseTelescope e f g (Telescope t) = Telescope <$>
  traverse (\(h, p, typ) -> (,,) h <$> e p <*> bitraverseScope f g typ) t

withTeleHints :: Telescope d expr v -> (Vector Name -> PrettyM a) -> PrettyM a
withTeleHints = withNameHints . teleNames

prettyTeleVars :: (HasRelevance d, HasPlicitness d)
               => Vector Name -> Telescope d expr v -> PrettyM Doc
prettyTeleVars ns t = hsep
  [ mappend (pure tilde) `iff` isIrrelevant p
  $ braces `iff` isImplicit p
  $ prettyM $ ns Vector.! i
  | (i, p) <- zip [0..] $ Vector.toList $ teleAnnotations t
  ]

prettyTeleVarTypes :: (Eq1 expr, Eq v, Eq d, Pretty (expr v), Monad expr, IsString v, HasRelevance d, HasPlicitness d)
                   => Vector Name -> Telescope d expr v -> PrettyM Doc
prettyTeleVarTypes ns (Telescope v) = hcat $ map go grouped
  where
    inst = instantiate $ pure . fromText . (ns Vector.!) . unTele
    vlist = Vector.toList v
    grouped = [ (n : [n' | (Hint n', _) <- vlist'], p, t)
              | (Hint n, (_, p, t)):vlist' <- List.group $ zip (map Hint [(0 :: Int)..]) vlist]
    go (xs, p, t)
      = (pure tilde <>) `iff` isIrrelevant p
      $ (if isImplicit p then braces else parens)
      $ hsep (map (prettyM . (ns Vector.!)) xs) <+> prettyM ":" <+> prettyM (inst t)

instance (Eq1 expr, Eq d, Eq v, Pretty (expr v), Monad expr, IsString v, HasRelevance d, HasPlicitness d)
  => Pretty (Telescope d expr v) where
  prettyM tele = withTeleHints tele $ \ns -> prettyTeleVarTypes ns tele

forTele :: Monad m
        => Telescope d expr a
        -> (NameHint -> d -> Scope Tele expr a -> m b)
        -> m (Vector b)
forTele (Telescope t) f = forM t $ \(h, d, s) -> f h d s

iforTele :: Monad m
         => Telescope d expr a
         -> (Int -> NameHint -> d -> Scope Tele expr a -> m b)
         -> m (Vector b)
iforTele (Telescope t) f = flip Vector.imapM t $ \i (h, d, s) -> f i h d s

instantiateTele :: Monad f => Vector (f a) -> Scope Tele f a -> f a
instantiateTele vs = instantiate ((vs Vector.!) . unTele)

teleAbstraction :: Eq a => Vector a -> a -> Maybe Tele
teleAbstraction vs = fmap Tele . (`Vector.elemIndex` vs)

-- | View consecutive bindings at the same time
bindingsViewM
  :: Monad expr
  => (forall v'. expr v' -> Maybe (NameHint, d, expr v', Scope1 expr v'))
  -> expr v -> Maybe (Telescope d expr v, Scope Tele expr v)
bindingsViewM f expr@(f -> Just _) = Just $ bindingsView f expr
bindingsViewM _ _ = Nothing

-- | View consecutive bindings at the same time
bindingsView
  :: Monad expr
  => (forall v'. expr v' -> Maybe (NameHint, d, expr v', Scope1 expr v'))
  -> expr v -> (Telescope d expr v, Scope Tele expr v)
bindingsView f expr = go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = (Telescope $ pure (n, p, toScope e) <> ns, s')
      where
        (Telescope ns, s') = (go $! x + 1) $ instantiate1 (return $ B x) s
    go _ e = (mempty, toScope e)
