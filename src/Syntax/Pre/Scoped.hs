{-# LANGUAGE GADTs, OverloadedStrings, PatternSynonyms, ViewPatterns #-}
module Syntax.Pre.Scoped
  ( module Definition
  , module Pattern
  , Expr(..), Type
  , clause, pi_, lam, case_
  , apps
  , appsView
  , piView
  , pattern Pi1
  ) where

import Control.Monad
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.Functor.Classes
import Data.Hashable
import Data.HashSet(HashSet)
import Data.Monoid
import Data.Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Syntax.Pre.Definition as Definition
import Syntax.Pre.Pattern as Pattern
import Util
import Util.Tsil

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con (HashSet QConstr)
  | Pi !Plicitness (Pat (HashSet QConstr) (PatternScope Type v) ()) (PatternScope Expr v)
  | Lam !Plicitness (Pat (HashSet QConstr) (PatternScope Type v) ()) (PatternScope Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Let (Vector (SourceLoc, NameHint, PatDefinition (Clause LetVar Expr v), Maybe (Scope LetVar Type v))) (Scope LetVar Expr v)
  | Case (Expr v) [(Pat (HashSet QConstr) (PatternScope Type v) (), PatternScope Expr v)]
  | ExternCode (Extern (Expr v))
  | Wildcard
  | SourceLoc !SourceLoc (Expr v)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
clause
  :: (Monad expr, Hashable v, Eq v)
  => Vector (Plicitness, Pat (HashSet QConstr) (expr v) v)
  -> expr v
  -> Clause void expr v
clause plicitPats e = do
  let pats = snd <$> plicitPats
      vars = join (toVector <$> pats)
      typedPats = second (void . first (mapBound B)) <$> abstractPatternsTypes vars plicitPats
  Clause typedPats $ abstract (fmap B . patternAbstraction vars) e

pi_
  :: (Hashable v, Eq v)
  => Plicitness
  -> Pat (HashSet QConstr) (Type v) v
  -> Expr v
  -> Expr v
pi_ p pat = Pi p (void $ abstractPatternTypes vs pat) . abstract (patternAbstraction vs)
    where
      vs = toVector pat

lam
  :: (Hashable v, Eq v)
  => Plicitness
  -> Pat (HashSet QConstr) (Type v) v
  -> Expr v
  -> Expr v
lam p pat = Lam p (void $ abstractPatternTypes vs pat) . abstract (patternAbstraction vs)
    where
      vs = toVector pat

case_
  :: (Hashable v, Eq v)
  => Expr v
  -> [(Pat (HashSet QConstr) (Type v) v, Expr v)]
  -> Expr v
case_ expr pats = Case expr $ go <$> pats
  where
    go (pat, e) = (void $ abstractPatternTypes vs pat, abstract (patternAbstraction vs) e)
      where
        vs = toVector pat

apps :: Foldable t => Expr v -> t (Plicitness, Expr v) -> Expr v
apps = Foldable.foldl' (uncurry . App)

piView :: Expr v -> Maybe (Plicitness, Pat (HashSet QConstr) (PatternScope Type v) (), PatternScope Expr v)
piView (Pi p pat s) = Just (p, pat, s)
piView _ = Nothing

appsView :: Expr v -> (Expr v, [(Plicitness, Expr v)])
appsView = second toList . go
  where
    go (SourceLoc _ e) = go e
    go (App e1 p e2) = second (`Snoc` (p, e2)) $ go e1
    go e = (e, Nil)

annoPatView
  :: Pat (HashSet QConstr) (Scope b Expr a) t
  -> (Pat (HashSet QConstr) (Scope b Expr a) t, Scope b Expr a)
annoPatView (PatLoc _ p) = annoPatView p
annoPatView (AnnoPat p t) = (p, t)
annoPatView p = (p, Scope Wildcard)

pattern Pi1
  :: NameHint
  -> Plicitness
  -> Expr v
  -> Scope1 Expr v
  -> Expr v
pattern Pi1 h p t s <- Pi p (annoPatView -> (varPatView -> Just h, unusedScope -> Just t)) (mapBound (\0 -> ()) -> s)
  where
    Pi1 h p Wildcard s = Pi p (VarPat h ()) $ mapBound (\() -> 0) s
    Pi1 h p t s = Pi p (AnnoPat (VarPat h ()) (abstractNone t)) $ mapBound (\() -> 0) s

-------------------------------------------------------------------------------
-- Instances
instance Eq1 Expr where
  liftEq f (Var v1) (Var v2) = f v1 v2
  liftEq _ (Global g1) (Global g2) = g1 == g2
  liftEq _ (Lit l1) (Lit l2) = l1 == l2
  liftEq _ (Con c1) (Con c2) = c1 == c2
  liftEq f (Pi p1 pat1 s1) (Pi p2 pat2 s2) = p1 == p2 && liftPatEq (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2
  liftEq f (Lam p1 pat1 s1) (Lam p2 pat2 s2) = p1 == p2 && liftPatEq (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2
  liftEq f (App e1 p1 e1') (App e2 p2 e2') = liftEq f e1 e2 && p1 == p2 && liftEq f e1' e2'
  liftEq f (Let tele1 s1) (Let tele2 s2) = liftEq (\(_, _, d1, mt1) (_, _, d2, mt2) -> liftEq (liftEq f) d1 d2 && liftEq (liftEq f) mt1 mt2) tele1 tele2 && liftEq f s1 s2
  liftEq f (Case e1 brs1) (Case e2 brs2)
    = liftEq f e1 e2
    && liftEq (\(pat1, s1) (pat2, s2) -> liftPatEq (==) (liftEq f) (==) pat1 pat2 && liftEq f s1 s2) brs1 brs2
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
    Let tele s -> Let ((\(loc, h, pd, mt) -> (loc, h, (>>>= f) <$> pd, (>>>= f) <$> mt)) <$> tele) (s >>>= f)
    Case e brs -> Case (e >>= f) (bimap (first (>>>= f)) (>>>= f) <$> brs)
    ExternCode c -> ExternCode ((>>= f) <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (e >>= f)

instance GBind Expr where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con _ -> expr
    Pi p pat s -> Pi p (first (gbound f) pat) (gbound f s)
    Lam p pat s -> Lam p (first (gbound f) pat) (gbound f s)
    App e1 p e2 -> App (gbind f e1) p (gbind f e2)
    Let tele s -> Let ((\(loc, h, pd, mt) -> (loc, h, gbound f <$> pd, gbound f <$> mt)) <$> tele) (gbound f s)
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
    Let tele s -> Let <$> traverse (bitraverse (traverse $ traverse f) $ traverse $ traverse f) tele <*> traverse f s
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
    Pi p pat s -> withNameHints (nameHints pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` arrPrec $
        prettyAnnotation p (prettyPattern ns $ first inst pat) <+> "->" <+>
          associate arrPrec (prettyM $ inst s)
    Lam p pat s -> withNameHints (nameHints pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` absPrec $
        "\\" <> prettyAnnotation p (prettyPattern ns $ first inst pat) <> "." <+>
          associate absPrec (prettyM $ inst s)
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Let clauses scope -> parens `above` letPrec $ withNameHints ((\(_, h, _, _) -> h) <$> clauses) $ \ns ->
      let go = ifor clauses $ \i (_, _, cl, mt) -> do
            let addTypeClause rest = case mt of
                  Nothing -> rest
                  Just t -> prettyM (ns Vector.! i) <+> ":" <+>
                    prettyM (instantiateLet (pure . fromName) ns t)
                    <$$> rest
            addTypeClause
              $ prettyNamed
                (prettyM $ ns Vector.! i)
                (instantiateLetClause (pure . fromName) ns <$> cl)
       in "let" <+> align (vcat go)
        <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns scope)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat $ prettyBranch <$> brs)
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
    where
      prettyBranch (pat, br) = withNameHints (nameHints pat) $ \ns -> do
        let inst = instantiatePattern (pure . fromName) ns
        prettyPattern ns (first inst pat) <+> "->" <+> prettyM (inst br)
