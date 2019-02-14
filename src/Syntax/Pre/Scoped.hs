{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
module Syntax.Pre.Scoped
  ( module Definition
  , module Pattern
  , module Pre
  , Expr(..), Type
  , clause, pi_, telePis, lam, case_
  , apps
  , appsView
  ) where

import Protolude hiding (Type)

import Data.Bitraversable
import Data.Foldable as Foldable
import Data.Functor.Classes
import Data.HashSet(HashSet)
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Syntax.Pre.Definition as Definition
import Syntax.Pre.Literal as Pre
import Syntax.Pre.Pattern as Pattern
import Util
import Util.Tsil

data Expr v
  = Var v
  | Global QName
  | Lit Pre.Literal
  | Con (HashSet QConstr)
  | Pi !Plicitness (Pat (HashSet QConstr) Pre.Literal (PatternScope Type v) NameHint) (PatternScope Expr v)
  | Lam !Plicitness (Pat (HashSet QConstr) Pre.Literal (PatternScope Type v) NameHint) (PatternScope Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Let (Vector (SourceLoc, NameHint, ConstantDef Expr (Var LetVar v))) (Scope LetVar Expr v)
  | Case (Expr v) [(Pat (HashSet QConstr) Pre.Literal (PatternScope Type v) NameHint, PatternScope Expr v)]
  | ExternCode (Extern (Expr v))
  | Wildcard
  | SourceLoc !SourceLoc (Expr v)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
clause
  :: (Monad expr, Hashable v, Eq v)
  => (v -> NameHint)
  -> Vector (Plicitness, Pat (HashSet QConstr) Pre.Literal (expr v) v)
  -> expr v
  -> Clause expr v
clause h plicitPats e = do
  let pats = snd <$> plicitPats
      vars = pats >>= toVector
      typedPats = fmap (fmap h) <$> abstractPatternsTypes vars plicitPats
  Clause typedPats $ abstract (patternAbstraction vars) e

pi_
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Plicitness
  -> Pat (HashSet QConstr) Pre.Literal (Type v) v
  -> Expr v
  -> Expr v
pi_ h p pat = Pi p (h <$> abstractPatternTypes vs pat) . abstract (patternAbstraction vs)
    where
      vs = toVector pat

pis
  :: (Hashable v, Eq v, Foldable t)
  => (v -> NameHint)
  -> t (Plicitness, Pat (HashSet QConstr) Pre.Literal (Type v) v)
  -> Expr v
  -> Expr v
pis h pats e = foldr (uncurry $ pi_ h) e pats

telePis
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Telescope Type v
  -> Expr v
  -> Expr v
telePis h tele e = fmap (unvar (panic "telePis") identity) $ pis h' pats $ F <$> e
  where
    h' = unvar (\(TeleVar v) -> teleHints tele Vector.! v) h
    pats = iforTele tele $ \i _ p s -> (p, AnnoPat (VarPat $ B $ TeleVar i) $ fromScope s)

lam
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Plicitness
  -> Pat (HashSet QConstr) Pre.Literal (Type v) v
  -> Expr v
  -> Expr v
lam h p pat = Lam p (h <$> abstractPatternTypes vs pat) . abstract (patternAbstraction vs)
    where
      vs = toVector pat

case_
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Expr v
  -> [(Pat (HashSet QConstr) Pre.Literal (Type v) v, Expr v)]
  -> Expr v
case_ h expr pats = Case expr $ go <$> pats
  where
    go (pat, e) = (h <$> abstractPatternTypes vs pat, abstract (patternAbstraction vs) e)
      where
        vs = toVector pat

apps :: Foldable t => Expr v -> t (Plicitness, Expr v) -> Expr v
apps = Foldable.foldl' (uncurry . App)

appsView :: Expr v -> (Expr v, [(Plicitness, Expr v)])
appsView = second toList . go
  where
    go (SourceLoc _ e) = go e
    go (App e1 p e2) = second (`Snoc` (p, e2)) $ go e1
    go e = (e, Nil)

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr where
  liftEq f (Var v1) (Var v2) = f v1 v2
  liftEq _ (Global g1) (Global g2) = g1 == g2
  liftEq _ (Lit l1) (Lit l2) = l1 == l2
  liftEq _ (Con c1) (Con c2) = c1 == c2
  liftEq f (Pi p1 pat1 s1) (Pi p2 pat2 s2) = p1 == p2 && liftPatEq (==) (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2
  liftEq f (Lam p1 pat1 s1) (Lam p2 pat2 s2) = p1 == p2 && liftPatEq (==) (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2
  liftEq f (App e1 p1 e1') (App e2 p2 e2') = liftEq f e1 e2 && p1 == p2 && liftEq f e1' e2'
  liftEq f (Let defs1 s1) (Let defs2 s2) = liftEq (\(_, _, d1) (_, _, d2) -> liftEq (liftEq f) d1 d2) defs1 defs2 && liftEq f s1 s2
  liftEq f (Case e1 brs1) (Case e2 brs2)
    = liftEq f e1 e2
    && liftEq (\(pat1, s1) (pat2, s2) -> liftPatEq (==) (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2) brs1 brs2
  liftEq f (ExternCode c) (ExternCode c') = liftEq (liftEq f) c c'
  liftEq _ Wildcard Wildcard = True
  liftEq f (SourceLoc _ e1) e2 = liftEq f e1 e2
  liftEq f e1 (SourceLoc _ e2) = liftEq f e1 e2
  liftEq _ _ _ = False

instance Eq v => Eq (Expr v) where
  (==) = liftEq (==)

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = case expr of
    Var v -> f v
    Global v -> Global v
    Lit l -> Lit l
    Con c -> Con c
    Pi p pat s -> Pi p (first (>>>= f) pat) ((>>>= f) s)
    Lam p pat s -> Lam p (first (>>>= f) pat) ((>>>= f) s)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Let defs s -> Let ((\(loc, h, pd) -> (loc, h, pd >>>= unvar (pure . B) (fmap F . f))) <$> defs) (s >>>= f)
    Case e brs -> Case (e >>= f) (bimap (first (>>>= f)) (>>>= f) <$> brs)
    ExternCode c -> ExternCode ((>>= f) <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (e >>= f)

instance GBind Expr QName where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con _ -> expr
    Pi p pat s -> Pi p (first (gbound f) pat) (gbound f s)
    Lam p pat s -> Lam p (first (gbound f) pat) (gbound f s)
    App e1 p e2 -> App (gbind f e1) p (gbind f e2)
    Let defs s -> Let ((\(loc, h, pd) -> (loc, h, gbound (fmap F . f) pd)) <$> defs) (gbound f s)
    Case e brs -> Case (gbind f e) (bimap (first (gbound f)) (gbound f) <$> brs)
    ExternCode c -> ExternCode (gbind f <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (gbind f e)

instance Functor Expr where fmap = fmapDefault
instance Foldable Expr where foldMap = foldMapDefault

instance Traversable Expr where
  traverse f expr = case expr of
    Var v -> Var <$> f v
    Global v -> pure $ Global v
    Lit l -> pure $ Lit l
    Con c -> pure $ Con c
    Pi p pat s -> Pi p <$> bitraverse (traverse f) pure pat <*> traverse f s
    Lam p pat s -> Lam p <$> bitraverse (traverse f) pure pat <*> traverse f s
    App e1 p e2 -> App <$> traverse f e1 <*> pure p <*> traverse f e2
    Let defs s -> Let <$> traverse (bitraverse pure $ traverse $ traverse f) defs <*> traverse f s
    Case e brs -> Case
      <$> traverse f e
      <*> traverse (bitraverse (bitraverse (traverse f) pure) (traverse f)) brs
    ExternCode c -> ExternCode <$> traverse (traverse f) c
    SourceLoc r e -> SourceLoc r <$> traverse f e
    Wildcard -> pure Wildcard

instance v ~ Doc => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c -> prettyM $ toList c
    Pi p (AnnoPat WildcardPat t) s -> parens `above` arrPrec $ do
      let inst = instantiatePattern (pure . fromName) mempty
      prettyAnnotation p (prettyM $ inst t) <+> "->" <+>
        associate arrPrec (prettyM $ inst s)
    Pi p pat s -> withNameHints (toVector pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` arrPrec $
        prettyAnnotation p (prettyPattern ns $ first inst pat) <+> "->" <+>
          associate arrPrec (prettyM $ inst s)
    Lam p pat s -> withNameHints (toVector pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` absPrec $
        "\\" <> prettyAnnotation p (prettyPattern ns $ first inst pat) <> "." <+>
          associate absPrec (prettyM $ inst s)
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Let defs scope -> parens `above` letPrec $ withNameHints ((\(_, h, _) -> h) <$> defs) $ \ns ->
      let go = ifor defs $ \i (_, _, cl) ->
            prettyNamed
              (prettyM $ ns Vector.! i)
              (instantiateConstantDef (pure . fromName . (ns Vector.!) . unLetVar) cl)
       in "let" <+> align (vcat go)
        <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns scope)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat $ prettyBranch <$> brs)
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
    where
      prettyBranch (pat, br) = withNameHints (toVector pat) $ \ns -> do
        let inst = instantiatePattern (pure . fromName) ns
        prettyPattern ns (first inst pat) <+> "->" <+> prettyM (inst br)
