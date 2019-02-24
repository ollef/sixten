{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Syntax.Core where

import Protolude hiding (Type, TypeRep)

import Data.Bifoldable
import Data.Bitraversable
import Data.Deriving
import Data.Foldable as Foldable
import Data.Vector(Vector)

import Effect
import qualified Effect.Context as Context
import Syntax
import TypeRep(TypeRep)
import Util
import Util.Tsil

-- | Expressions with meta-variables of type @m@ and variables of type @v@.
data Expr m v
  = Var v
  | Meta m (Vector (Plicitness, Expr m v))
  | Global GName
  | Con QConstr
  | Lit Literal
  | Pi !NameHint !Plicitness (Type m v) (Scope1 (Expr m) v)
  | Lam !NameHint !Plicitness (Type m v) (Scope1 (Expr m) v)
  | App (Expr m v) !Plicitness (Expr m v)
  | Let (LetRec (Expr m) v) (Scope LetVar (Expr m) v)
  | Case (Expr m v) (Branches (Expr m) v) (Type m v)
  | ExternCode (Extern (Expr m v)) (Type m v)
  | SourceLoc !SourceLoc (Expr m v)
  deriving (Foldable, Functor, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
unSourceLoc :: Expr m v -> Expr m v
unSourceLoc (SourceLoc _ e) = unSourceLoc e
unSourceLoc e = e

sourceLocView :: Expr m v -> (SourceLoc, Expr m v)
sourceLocView (SourceLoc loc (unSourceLoc -> e)) = (loc, e)
sourceLocView e = (noSourceLoc "sourceLocView", e)

lam
  :: MonadContext (Expr meta Var) m
  => Var
  -> Expr meta Var
  -> m (Expr meta Var)
lam v e = do
  Context.Binding h p t _ <- Context.lookup v
  return $ Lam h p t $ abstract1 v e

plicitLam
  :: MonadContext (Expr meta Var) m
  => Plicitness
  -> Var
  -> Expr meta Var
  -> m (Expr meta Var)
plicitLam p v e = do
  Context.Binding h _ t _ <- Context.lookup v
  return $ Lam h p t $ abstract1 v e

pi_
  :: MonadContext (Expr meta Var) m
  => Var
  -> Expr meta Var
  -> m (Expr meta Var)
pi_ v e = do
  Context.Binding h p t _ <- Context.lookup v
  return $ Pi h p t $ abstract1 v e

plicitPi
  :: MonadContext (Expr meta Var) m
  => Plicitness
  -> Var
  -> Expr meta Var
  -> m (Expr meta Var)
plicitPi p v e = do
  Context.Binding h _ t _ <- Context.lookup v
  return $ Pi h p t $ abstract1 v e

lams
  :: (MonadContext (Expr meta Var) m, Foldable t)
  => t Var
  -> Expr meta Var
  -> m (Expr meta Var)
lams xs e = foldrM lam e xs

plicitLams
  :: (MonadContext (Expr meta Var) m, Foldable t)
  => t (Plicitness, Var)
  -> Expr meta Var
  -> m (Expr meta Var)
plicitLams xs e = foldrM (uncurry plicitLam) e xs

pis
  :: (MonadContext (Expr meta Var) m, Foldable t)
  => t Var
  -> Expr meta Var
  -> m (Expr meta Var)
pis xs e = foldrM pi_ e xs

plicitPis
  :: (MonadContext (Expr meta Var) m, Foldable t)
  => t (Plicitness, Var)
  -> Expr meta Var
  -> m (Expr meta Var)
plicitPis xs e = foldrM (uncurry plicitPi) e xs

let_
  :: MonadContext (Expr meta Var) m
  => Vector (Var, SourceLoc, Expr meta Var)
  -> Expr meta Var
  -> m (Expr meta Var)
let_ ds body = do
  context <- getContext
  let abstr = letAbstraction $ fst3 <$> ds
      ds' = LetRec
        [ LetBinding h loc (abstract abstr e) t
        | (v, loc, e) <- ds
        , let Context.Binding h _ t _ = Context.lookup v context
        ]
  return $ Let ds' $ abstract abstr body

pattern MkType :: TypeRep -> Expr m v
pattern MkType rep = Lit (TypeRep rep)

apps :: Foldable t => Expr m v -> t (Plicitness, Expr m v) -> Expr m v
apps = Foldable.foldl' (uncurry . App)

appsView :: Expr m v -> (Expr m v, [(Plicitness, Expr m v)])
appsView = second toList . go
  where
    go (unSourceLoc -> App e1 p e2) = second (`Snoc` (p, e2)) $ go e1
    go e = (e, Nil)

varView :: Expr m a -> Maybe a
varView (unSourceLoc -> Var v) = Just v
varView _ = Nothing

distinctVarView :: (Eq v, Hashable v, Traversable t) => t (p, Expr m v) -> Maybe (t (p, v))
distinctVarView es = case traverse (traverse varView) es of
  Just es' | distinct (snd <$> es') -> Just es'
  _ -> Nothing

piView :: Expr m v -> Maybe (NameHint, Plicitness, Type m v, Scope1 (Expr m) v)
piView (unSourceLoc -> Pi h a t s) = Just (h, a, t, s)
piView _ = Nothing

lamView :: Expr m v -> Maybe (NameHint, Plicitness, Type m v, Scope1 (Expr m) v)
lamView (unSourceLoc -> Lam h a t s) = Just (h, a, t, s)
lamView _ = Nothing

typeApp :: Expr m v -> Plicitness -> Expr m v -> Maybe (Expr m v)
typeApp (piView -> Just (_, p, _, s)) p' e | p == p' = Just $ Util.instantiate1 e s
typeApp _ _ _ = Nothing

typeApps :: Foldable t => Expr m v -> t (Plicitness, Expr m v) -> Maybe (Expr m v)
typeApps = foldlM (\e (p, e') -> typeApp e p e')

usedPiView
  :: Expr m v
  -> Maybe (NameHint, Plicitness, Expr m v, Scope1 (Expr m) v)
usedPiView (piView -> Just (n, p, e, s@(unusedScope -> Nothing))) = Just (n, p, e, s)
usedPiView _ = Nothing

usedPisViewM :: Expr m v -> Maybe (Telescope (Expr m) v, Scope TeleVar (Expr m) v)
usedPisViewM = bindingsViewM usedPiView

piTelescope :: Expr m v -> Telescope (Expr m) v
piTelescope (pisView -> (tele, _)) = tele

pisView :: Expr m v -> (Telescope (Expr m) v, Scope TeleVar (Expr m) v)
pisView = bindingsView piView

lamsViewM :: Expr m v -> Maybe (Telescope (Expr m) v, Scope TeleVar (Expr m) v)
lamsViewM = bindingsViewM lamView

arrow :: Plicitness -> Expr m v -> Expr m v -> Expr m v
arrow p a b = Pi mempty p a $ abstractNone b

quantifiedConstrTypes
  :: DataDef (Type m) v
  -> [ConstrDef (Type m v)]
quantifiedConstrTypes (DataDef ps cs) = map (fmap $ quantify Pi ps') cs
  where
    ps' = mapPlics implicitise ps

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance Applicative (Expr m) where
  pure = return
  (<*>) = ap

instance Monad (Expr m) where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Meta m vs -> Meta m $ second (>>= f) <$> vs
    Global v -> Global v
    Con c -> Con c
    Lit l -> Lit l
    Pi h a t s -> Pi h a (t >>= f) (s >>>= f)
    Lam h a t s -> Lam h a (t >>= f) (s >>>= f)
    App e1 a e2 -> App (e1 >>= f) a (e2 >>= f)
    Let ds scope -> Let (ds >>>= f) (scope >>>= f)
    Case e brs retType -> Case (e >>= f) (brs >>>= f) (retType >>= f)
    ExternCode c t -> ExternCode ((>>= f) <$> c) (t >>= f)
    SourceLoc loc e -> SourceLoc loc (e >>= f)

instance GBind (Expr m) GName where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Meta m es -> Meta m (second (gbind f) <$> es)
    Global v -> f v
    Con _ -> expr
    Lit _ -> expr
    Pi h a t s -> Pi h a (gbind f t) (gbound f s)
    Lam h a t s -> Lam h a (gbind f t) (gbound f s)
    App e1 a e2 -> App (gbind f e1) a (gbind f e2)
    Let ds scope -> Let (gbound f ds) (gbound f scope)
    Case e brs retType -> Case (gbind f e) (gbound f brs) (gbind f retType)
    ExternCode c t -> ExternCode (gbind f <$> c) (gbind f t)
    SourceLoc loc e -> SourceLoc loc (gbind f e)

instance Bifunctor Expr where bimap = bimapDefault
instance Bifoldable Expr where bifoldMap = bifoldMapDefault
instance Bitraversable Expr where
  bitraverse f g expr = case expr of
    Var v -> Var <$> g v
    Meta m es -> Meta <$> f m <*> traverse (traverse $ bitraverse f g) es
    Global v -> pure $ Global v
    Con c -> pure $ Con c
    Lit l -> pure $ Lit l
    Pi h a t s -> Pi h a <$> bitraverse f g t <*> bitraverseScope f g s
    Lam h a t s -> Lam h a <$> bitraverse f g t <*> bitraverseScope f g s
    App e1 a e2 -> App <$> bitraverse f g e1 <*> pure a <*> bitraverse f g e2
    Let ds scope -> Let <$> bitraverseLet f g ds <*> bitraverseScope f g scope
    Case e brs retType -> Case <$> bitraverse f g e <*> bitraverseBranches f g brs <*> bitraverse f g retType
    ExternCode c t -> ExternCode <$> traverse (bitraverse f g) c <*> bitraverse f g t
    SourceLoc loc e -> SourceLoc loc <$> bitraverse f g e

hoistMetas
  :: Monad f
  => (forall a. meta -> Vector (Plicitness, Expr meta' a) -> f (Expr meta' a))
  -> Expr meta v
  -> f (Expr meta' v)
hoistMetas f expr = case expr of
  Var v -> pure $ Var v
  Meta m es -> f m =<< traverse (traverse $ hoistMetas f) es
  Global v -> pure $ Global v
  Con c -> pure $ Con c
  Lit l -> pure $ Lit l
  Pi h a t s -> Pi h a <$> hoistMetas f t <*> transverseScope (hoistMetas f) s
  Lam h a t s -> Lam h a <$> hoistMetas f t <*> transverseScope (hoistMetas f) s
  App e1 a e2 -> App <$> hoistMetas f e1 <*> pure a <*> hoistMetas f e2
  Let ds scope -> Let <$> transverseLet (hoistMetas f) ds <*> transverseScope (hoistMetas f) scope
  Case e brs retType -> Case <$> hoistMetas f e <*> transverseBranches (hoistMetas f) brs <*> hoistMetas f retType
  ExternCode c t -> ExternCode <$> traverse (hoistMetas f) c <*> hoistMetas f t
  SourceLoc loc e -> SourceLoc loc <$> hoistMetas f e

hoistMetas_
  :: Monad f
  => (meta -> f ())
  -> Expr meta v
  -> f ()
hoistMetas_ f = void . hoistMetas (\m es -> Meta m es <$ f m)

instance (v ~ Doc, Pretty m, Eq m) => Pretty (Expr m v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Meta m es -> prettyApps (prettyM m) ((\(p, e) -> prettyAnnotation p $ prettyM e) <$> es)
    Global g -> prettyM g
    Con c -> prettyM c
    Lit l -> prettyM l
    Pi _ a t (unusedScope -> Just e) -> parens `above` arrPrec $
      prettyAnnotation a (prettyM t)
      <+> "->" <+>
      associate arrPrec (prettyM e)
    (usedPisViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` arrPrec $
      prettyTeleVarTypes ns tele <+> "->" <+>
      associate arrPrec (prettyM $ instantiateTele (pure . fromName) ns s)
    Pi {} -> panic "impossible prettyPrec pi"
    (lamsViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      "\\" <> prettyTeleVarTypes ns tele <> "." <+>
      prettyM (instantiateTele (pure . fromName) ns s)
    Lam {} -> panic "impossible prettyPrec lam"
    App e1 a e2 -> prettyApp (prettyM e1) (prettyAnnotation a $ prettyM e2)
    Let ds s -> parens `above` letPrec $ withLetHints ds $ \ns ->
      "let" <+> align (prettyLet ns ds)
      <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns s)
    Case e brs retType -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <+> parens (prettyM retType)
        <$$> Syntax.indent 2 (prettyM brs)
    ExternCode c t -> parens `above` annoPrec $
      prettyM c <+> ":" <+> prettyM t
    SourceLoc _ e -> prettyM e
