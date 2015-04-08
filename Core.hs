{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, Rank2Types, ViewPatterns #-}
module Core where

import Bound
import Bound.Scope
import Bound.Var
import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Data.List as List
import qualified Data.Set as S
import Data.String
import Data.Traversable as T
import Prelude.Extras

import Branches
import Pretty
import Util

data Expr v
  = Var v
  | Type -- Int
  | Pi  !NameHint !Plicitness (Type v) (Scope1 Expr v)
  | Lam !NameHint !Plicitness (Type v) (Scope1 Expr v)
  | App  (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches Expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- * Views
-- | View consecutive bindings at the same time
bindingsView
  :: (forall v'. Expr v' -> Maybe (NameHint, Plicitness, Type v', Scope1 Expr v'))
  -> Expr v -> Maybe ([(NameHint, Plicitness, Type (Var Int v))], Scope Int Expr v)
bindingsView f expr@(f -> Just _) = Just $ go 0 $ F <$> expr
  where
    go x (f -> Just (n, p, e, s)) = ((n, p, e) : ns, s')
      where
        (ns, s') = (go $! (x + 1)) (instantiate1 (return $ B x) s)
    go _ e = ([], toScope e)
bindingsView _ _ = Nothing

piView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
piView (Pi n p e s) = Just (n, p, e, s)
piView _            = Nothing

usedPiView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
usedPiView (Pi n p e s@(unusedScope -> Nothing)) = Just (n, p, e, s)
usedPiView _                                     = Nothing

lamView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
lamView (Lam n p e s) = Just (n, p, e, s)
lamView _             = Nothing

appsView :: Expr v -> (Expr v, [(Plicitness, Expr v)])
appsView = second reverse . go
  where
    go (App e1 p e2) = (e1', (p, e2) : es)
      where (e1', es) = go e1
    go e = (e, [])

apps :: Expr v -> [(Plicitness, Expr v)] -> Expr v
apps = foldl (uncurry . App)

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr; instance Ord1 Expr; instance Show1 Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v       -> f v
    Type        -> Type
    Pi  x p t s -> Pi x p (t >>= f) (s >>>= f)
    Lam x p t s -> Lam x p (t >>= f) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyPrec expr = case expr of
    Var v     -> prettyPrec v
    Type      -> pure $ text "Type"
    Pi  _ p t (unusedScope -> Just e) -> parens `above` arrPrec $ do
      a <- bracesWhen (p == Implicit) $ prettyPrec t
      b <- associate $ prettyPrec e
      return $ a <+> text "->" <+> b
    (bindingsView usedPiView -> Just (hpts, s)) -> binding (\x -> text "forall" <+> x <> text ".") hpts s
    Pi {} -> error "impossible prettyPrec pi"
    (bindingsView lamView -> Just (hpts, s)) -> binding (\x -> text "\\" <> x <> text ".") hpts s
    Lam {} -> error "impossible prettyPrec lam"
    App e1 p e2 -> prettyApp (prettyPrec e1) (bracesWhen (p == Implicit) $ prettyPrec e2)
    Case _ _ -> undefined
    where
      binding doc hpts s = parens `above` absPrec $ do
        let hs = [h | (h, _, _) <- hpts]
        withHints hs $ \f -> do
          let grouped = [ (n : [n' | (Hint n', _) <- hpts'], p, t)
                        | (Hint n, (_, p, t)):hpts' <- List.group $ zip (map Hint [0..]) hpts]
              go (map (text . f) -> xs, p, t) =
                ((if p == Implicit then braces else parens) . ((hsep xs <+> text ":") <+>)) <$>
                prettyPrec (unvar (fromString . f) id <$> t)
          vs <- inviolable $ hcat <$> T.mapM go grouped
          b  <- associate $ prettyPrec $ instantiate (return . fromString . f) s
          return $ doc vs <+> b

etaLam :: Ord v => Hint (Maybe Name) -> Plicitness -> Expr v -> Scope1 Expr v -> Expr v
etaLam _ p _ (Scope (Core.App e p' (Var (B ()))))
  | B () `S.notMember` foldMap S.singleton e && p == p'
    = join $ unvar (error "etaLam impossible") id <$> e
etaLam n p t s = Core.Lam n p t s

betaApp :: Expr v -> Plicitness -> Expr v -> Expr v
betaApp e1@(Lam _ p1 _ s) p2 e2 | p1 == p2 = case (e2, bindings s) of
  (Var _, _) -> instantiate1 e2 s
  (_, _:_:_) -> App e1 p1 e2
  _          -> instantiate1 e2 s

betaApp e1 p e2 = App e1 p e2
