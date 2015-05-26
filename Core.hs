{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Core where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad
import Data.Bifunctor
import Data.HashMap.Lazy(HashMap)
import Data.Monoid
import Data.List as List
import qualified Data.Set as S
import Data.String
import Data.Traversable as T
import Prelude.Extras

import Annotation
import Branches
import Hint
import Pretty
import Util

-- | Expressions with variables of type @v@, with abstractions and applications
-- decorated by @d@s.
data Expr d v
  = Var v
  | Type -- Int
  | Pi  !NameHint !d (Type d v) (Scope1 (Expr d) v)
  | Lam !NameHint !d (Type d v) (Scope1 (Expr d) v)
  | App  (Expr d v) !d (Expr d v)
  | Case (Expr d v) (Branches (Expr d) v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Bifunctor Expr where
  bimap f g expr = case expr of
    Var v       -> Var $ g v
    Type        -> Type
    Pi  x d t s -> Pi  x (f d) (bimap f g t) $ bimapScope f g s
    Lam x d t s -> Lam x (f d) (bimap f g t) $ bimapScope f g s
    App e1 d e2 -> App (bimap f g e1) (f d) (bimap f g e2)
    Case _ _    -> undefined -- TODO

-- | Synonym for documentation purposes
type Type = Expr

type Program d v = HashMap v (Expr d v, Type d v, d)

-------------------------------------------------------------------------------
-- * Views
-- | View consecutive bindings at the same time
bindingsView
  :: (forall v'. Expr d v' -> Maybe (NameHint, d, Type d v', Scope1 (Expr d) v'))
  -> Expr d v -> Maybe ([(NameHint, d, Type d (Var Int v))], Scope Int (Expr d) v)
bindingsView f expr@(f -> Just _) = Just $ go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = ((n, p, e) : ns, s')
      where
        (ns, s') = (go $! (x + 1)) (instantiate1 (return $ B x) s)
    go _ e = ([], toScope e)
bindingsView _ _ = Nothing

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
    Type        -> Type
    Pi  x p t s -> Pi x p (t >>= f) (s >>>= f)
    Lam x p t s -> Lam x p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)

instance (Eq v, Eq d, HasPlicitness d, HasRelevance d, IsString v, Pretty v)
      => Pretty (Expr d v) where
  prettyPrec expr = case expr of
    Var v     -> prettyPrec v
    Type      -> pure $ text "Type"
    Pi  _ p t (unusedScope -> Just e) -> parens `above` arrPrec $ do
      a <- tildeWhen (isIrrelevant p) $ bracesWhen (isImplicit p) $ prettyPrec t
      b <- associate $ prettyPrec e
      return $ a <+> text "->" <+> b
    (bindingsView usedPiView -> Just (hpts, s)) -> binding (\x -> text "forall" <+> x <> text ".") hpts s
    Pi {} -> error "impossible prettyPrec pi"
    (bindingsView lamView -> Just (hpts, s)) -> binding (\x -> text "\\" <> x <> text ".") hpts s
    Lam {} -> error "impossible prettyPrec lam"
    App e1 p e2 -> prettyApp (prettyPrec e1) (tildeWhen (isIrrelevant p) $ bracesWhen (isImplicit p) $ prettyPrec e2)
    Case _ _ -> undefined
    where
      binding doc hpts s = parens `above` absPrec $ do
        let hs = [h | (h, _, _) <- hpts]
        withHints hs $ \f -> do
          let grouped = [ (n : [n' | (Hint n', _) <- hpts'], p, t)
                        | (Hint n, (_, p, t)):hpts' <- List.group $ zip (map Hint [0..]) hpts]
              go (map (text . f) -> xs, p, t) = tildeWhen (isIrrelevant p) $
                ( (if isImplicit p then braces else parens)
                . ((hsep xs <+> text ":") <+>)) <$>
                prettyPrec (unvar (fromString . f) id <$> t)
          vs <- inviolable $ hcat <$> T.mapM go grouped
          b  <- associate $ prettyPrec $ instantiate (return . fromString . f) s
          return $ doc vs <+> b

etaLam :: (Ord v, HasPlicitness d)
       => Hint (Maybe Name) -> d -> Expr d v -> Scope1 (Expr d) v -> Expr d v
etaLam _ p _ (Scope (Core.App e p' (Var (B ()))))
  | B () `S.notMember` toSet (second (const ()) <$> e) && plicitness p == plicitness p'
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n p t s = Core.Lam n p t s

betaApp :: Eq d => Expr d v -> d -> Expr d v -> Expr d v
betaApp e1@(Lam _ p1 _ s) p2 e2 | p1 == p2 = case (e2, bindings s) of
  -- (Var _, _) -> instantiate1 e2 s
  (_, _:_:_) -> App e1 p1 e2
  _          -> instantiate1 e2 s
betaApp e1 p e2 = App e1 p e2
