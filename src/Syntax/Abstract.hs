{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Syntax.Abstract where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Monoid
import Data.List as List
import qualified Data.Set as S
import Data.String
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax.Annotation
import Syntax.Branches
import Syntax.Hint
import Syntax.Pretty
import Util

-- | Expressions with variables of type @v@, with abstractions and applications
-- decorated by @d@s.
data Expr d v
  = Var v
  | Global Name
  | Con Constr
  | Type
  | Pi  !NameHint !d (Type d v) (Scope1 (Expr d) v)
  | Lam !NameHint !d (Type d v) (Scope1 (Expr d) v)
  | App  (Expr d v) !d (Expr d v)
  | Case (Expr d v) (Branches (Expr d) v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- * Views and smart constructors
piView :: Expr d v -> Maybe (NameHint, d, Type d v, Scope1 (Expr d) v)
piView (Pi n p e s) = Just (n, p, e, s)
piView _            = Nothing

usedPiView :: Expr d v -> Maybe (NameHint, d, Type d v, Scope1 (Expr d) v)
usedPiView (Pi n p e s@(unusedScope -> Nothing)) = Just (n, p, e, s)
usedPiView _                                     = Nothing

lamView :: Expr d v -> Maybe (NameHint, d, Type d v, Scope1 (Expr d) v)
lamView (Lam n p e s) = Just (n, p, e, s)
lamView _             = Nothing

appsView :: Expr d v -> (Expr d v, [(d, Expr d v)])
appsView = second reverse . go
  where
    go (App e1 p e2) = (e1', (p, e2) : es)
      where (e1', es) = go e1
    go e = (e, [])

apps :: Expr d v -> [(d, Expr d v)] -> Expr d v
apps = foldl (uncurry . App)

globals :: Expr d v -> Expr d (Var Name v)
globals expr = case expr of
  Var v       -> Var $ F v
  Global g    -> Var $ B g
  Con c       -> Con c
  Type        -> Type
  Pi  x p t s -> Pi x p (globals t) (exposeScope globals s)
  Lam x p t s -> Lam x p (globals t) (exposeScope globals s)
  App e1 p e2 -> App (globals e1) p (globals e2)
  Case e brs  -> Case (globals e) (exposeBranches globals brs)

-------------------------------------------------------------------------------
-- Instances
instance Eq d => Eq1 (Expr d)
instance Ord d => Ord1 (Expr d)
instance Show d => Show1 (Expr d)

instance Applicative (Expr d) where
  pure = return
  (<*>) = ap

instance Monad (Expr d) where
  return = Var
  expr >>= f = case expr of
    Var v       -> f v
    Global g    -> Global g
    Con c       -> Con c
    Type        -> Type
    Pi  x p t s -> Pi x p (t >>= f) (s >>>= f)
    Lam x p t s -> Lam x p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)

instance Bifunctor Expr where
  bimap = bimapDefault

instance Bifoldable Expr where
  bifoldMap = bifoldMapDefault

instance Bitraversable Expr where
  bitraverse f g expr = case expr of
    Var v       -> Var <$> g v
    Global v    -> pure $ Global v
    Con c       -> pure $ Con c
    Type        -> pure Type
    Pi  x d t s -> Pi  x <$> f d <*> bitraverse f g t <*> bitraverseScope f g s
    Lam x d t s -> Lam x <$> f d <*> bitraverse f g t <*> bitraverseScope f g s
    App e1 d e2 -> App <$> bitraverse f g e1 <*> f d <*> bitraverse f g e2
    Case e brs  -> Case <$> bitraverse f g e <*> bitraverseBranches f g brs

instance (Eq v, Eq d, HasPlicitness d, HasRelevance d, IsString v, Pretty v)
      => Pretty (Expr d v) where
  prettyM expr = case expr of
    Var v     -> prettyM v
    Global g  -> prettyM g
    Con c     -> prettyM c
    Type      -> pure $ text "Type"
    Pi  _ p t (unusedScope -> Just e) -> parens `above` arrPrec $
      ((pure tilde <>) `iff` isIrrelevant p $ braces `iff` isImplicit p $ prettyM t)
      <+> prettyM "->" <+>
      associate (prettyM e)
    (bindingsViewM usedPiView -> Just (hpts, s)) -> binding (\x -> prettyM "forall" <+> x <> prettyM ".") hpts s
    Pi {} -> error "impossible prettyPrec pi"
    (bindingsViewM lamView -> Just (hpts, s)) -> binding (\x -> prettyM "\\" <> x <> prettyM ".") hpts s
    Lam {} -> error "impossible prettyPrec lam"
    App e1 p e2 -> prettyApp (prettyM e1) ((pure tilde <>) `iff` isIrrelevant p $ braces `iff` isImplicit p $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+> prettyM "of" <$$> prettyM brs
    where
      binding doc hpts s = parens `above` absPrec $ do
        let hs = Vector.fromList $ fmap (\(h, _, _) -> h) hpts
        withNameHints hs $ \ns -> do
          let grouped = [ (n : [n' | (Hint n', _) <- hpts'], p, t)
                        | (Hint n, (_, p, t)):hpts' <- List.group $ zip (map Hint [(0 :: Int)..]) hpts]
              go (xs, p, t) = (pure tilde <>) `iff` isIrrelevant p $
                (if isImplicit p then braces else parens) $
                hsep (map (prettyM . (ns Vector.!)) xs) <+> prettyM ":" <+>
                prettyM (instantiate (pure . fromText . (ns Vector.!)) t)
          doc (inviolable $ hcat $ map go grouped) <+>
            associate (prettyM $ instantiate (pure . fromText . (ns Vector.!)) s)


etaLamM :: (Ord v, Monad m)
        => (d -> d -> m Bool)
        -> Hint (Maybe Name) -> d -> Expr d v -> Scope1 (Expr d) v -> m (Expr d v)
etaLamM isEq n p t s@(Scope (App e p' (Var (B ()))))
  | B () `S.notMember` toSet (second (const ()) <$> e) = do
    eq <- isEq p p'
    return $ if eq then
      join $ unvar (error "etaLam impossible") id <$> e
    else
      Lam n p t s
etaLamM _ n p t s = return $ Lam n p t s

etaLam :: Eq d
       => Hint (Maybe Name) -> d -> Expr d v -> Scope1 (Expr d) v -> Expr d v
etaLam _ p _ (Scope (App e p' (Var (B ()))))
  | B () `S.notMember` toSet (second (const ()) <$> e) && p == p'
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n p t s = Lam n p t s

betaApp :: Eq d => Expr d v -> d -> Expr d v -> Expr d v
betaApp e1@(Lam _ p1 _ s) p2 e2 | p1 == p2 = case bindings s of
  []  -> instantiate1 e2 s
  [_] -> instantiate1 e2 s
  _   -> App e1 p1 e2
betaApp e1 p e2 = App e1 p e2
