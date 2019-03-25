{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
module Syntax.Pre.Scoped
  ( module Definition
  , module Pre
  , Expr(..), Type
  , clause, pi_, telePis, lam, case_
  , apps
  , appsView
  , LetRec(..), LetBinding(..), Branches(..), Branch(..)
  ) where

import Protolude hiding (Type)

import qualified Bound
import Data.Bifoldable
import Data.Deriving
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.Functor.Classes
import Data.Hashable.Lifted
import Data.HashSet(HashSet)
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax hiding (Branches, LetBinding, LetRec, Pat)
import qualified Syntax
import Syntax.Pre.Definition as Definition
import Syntax.Pre.Literal as Pre
import Util
import Util.Tsil

data Expr v
  = Var v
  | Global QName
  | Lit Pre.Literal
  | Con (HashSet QConstr)
  | Pi !Plicitness (Pat Expr v) (PatternScope Expr v)
  | Lam !Plicitness (Pat Expr v) (PatternScope Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Let (LetRec Expr v) (Scope LetVar Expr v)
  | Case (Expr v) (Branches Expr v)
  | ExternCode (Extern (Expr v))
  | Wildcard
  | SourceLoc !SourceLoc (Expr v)
  deriving (Generic, Hashable, Generic1, Hashable1, Functor, Foldable, Traversable)

type Pat expr v = Syntax.Pat (HashSet QConstr) Pre.Literal NameHint (PatternScope expr v)

newtype Branches expr v = Branches [Branch expr v]
  deriving (Generic, Hashable, Generic1, Hashable1, Functor, Foldable, Traversable, Eq)

data Branch expr v = Branch !SourceLoc (Pat expr v) (PatternScope expr v)
  deriving (Generic, Hashable, Generic1, Hashable1, Functor, Foldable, Traversable, Eq)

newtype LetRec expr v = LetRec (Vector (LetBinding expr v))
  deriving (Generic, Hashable, Generic1, Hashable1, Functor, Foldable, Traversable)

data LetBinding expr v = LetBinding !SourceLoc !NameHint (ConstantDef expr (Bound.Var LetVar v))
  deriving (Generic, Generic1, Hashable1, Functor, Foldable, Traversable)

deriving instance (Monad expr, Eq (expr (Bound.Var LetVar v)), Eq v, Eq1 expr) => Eq (LetBinding expr v)
deriving instance (Monad expr, Eq (expr (Bound.Var LetVar v)), Eq v, Eq1 expr) => Eq (LetRec expr v)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
clause
  :: (Monad expr, Hashable v, Eq v)
  => SourceLoc
  -> (v -> NameHint)
  -> Vector (Plicitness, Syntax.Pat (HashSet QConstr) Pre.Literal v (expr v))
  -> expr v
  -> Clause expr v
clause loc h plicitPats e = do
  let
    pats = snd <$> plicitPats
    vars = pats >>= bifoldMap pure mempty
    typedPats = fmap (bimap h abstr) <$> plicitPats
    abstr = abstract $ patternAbstraction vars
  Clause loc typedPats $ abstr e

pi_
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Plicitness
  -> Syntax.Pat (HashSet QConstr) Pre.Literal v (Expr v)
  -> Expr v
  -> Expr v
pi_ h p pat = Pi p (bimap h abstr pat) . abstr
  where
    abstr = abstract $ patternAbstraction vs
    vs = bifoldMap pure mempty pat

pis
  :: (Hashable v, Eq v, Foldable t)
  => (v -> NameHint)
  -> t (Plicitness, Syntax.Pat (HashSet QConstr) Pre.Literal v (Expr v))
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
  -> Syntax.Pat (HashSet QConstr) Pre.Literal v (Type v)
  -> Expr v
  -> Expr v
lam h p pat = Lam p (bimap h abstr pat) . abstr
    where
      abstr = abstract $ patternAbstraction vs
      vs = bifoldMap pure mempty pat

case_
  :: (Hashable v, Eq v)
  => (v -> NameHint)
  -> Expr v
  -> [(SourceLoc, Syntax.Pat (HashSet QConstr) Pre.Literal v (Type v), Expr v)]
  -> Expr v
case_ h expr pats = Case expr $ Branches $ go <$> pats
  where
    go (loc, pat, e) = Branch loc (bimap h abstr pat) (abstr e)
      where
        abstr = abstract $ patternAbstraction vs
        vs = bifoldMap pure mempty pat

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
    Pi p pat s -> Pi p ((>>>= f) <$> pat) (s >>>= f)
    Lam p pat s -> Lam p ((>>>= f) <$> pat) (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Let defs s -> Let (defs >>>= f)  (s >>>= f)
    Case e brs -> Case (e >>= f) (brs >>>= f)
    ExternCode c -> ExternCode ((>>= f) <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (e >>= f)

instance Bound Branches where
  Branches brs >>>= f = Branches $ (>>>= f) <$> brs

instance Bound Branch where
  Branch loc pat s >>>= f = Branch loc ((>>>= f) <$> pat) $ s >>>= f

instance Bound LetRec where
  LetRec ds >>>= f = LetRec $ (>>>= f) <$> ds

instance Bound LetBinding where
  LetBinding loc h def >>>= f = LetBinding loc h $ def >>>= bitraverse pure f

instance GBound Branches where
  gbound f (Branches brs) = Branches $ gbound f <$> brs

instance GBound Branch where
  gbound f (Branch loc pat s) = Branch loc (gbound f <$> pat) (gbound f s)

instance GBound LetRec where
  gbound f (LetRec ds) = LetRec $ gbound f <$> ds

instance GBound LetBinding where
  gbound f (LetBinding loc h def) = LetBinding loc h $ gbound (fmap pure . f) def

instance (Monad expr, Hashable1 expr, Hashable v) => Hashable (LetBinding expr v) where
  hashWithSalt salt (LetBinding loc h cd)
    = liftHashWithSalt
      hashWithSalt
      (salt `hashWithSalt` loc `hashWithSalt` h)
      cd

instance GBind Expr QName where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con _ -> expr
    Pi p pat s -> Pi p (gbound f <$> pat) (gbound f s)
    Lam p pat s -> Lam p (gbound f <$> pat) (gbound f s)
    App e1 p e2 -> App (gbind f e1) p (gbind f e2)
    Let defs s -> Let (gbound f defs) (gbound f s)
    Case e brs -> Case (gbind f e) (gbound f brs)
    ExternCode c -> ExternCode (gbind f <$> c)
    Wildcard -> Wildcard
    SourceLoc r e -> SourceLoc r (gbind f e)

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
    Pi p pat s -> withNameHints (bifoldMap pure mempty pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` arrPrec $
        prettyAnnotation p (prettyPattern ns $ inst <$> pat) <+> "->" <+>
          associate arrPrec (prettyM $ inst s)
    Lam p pat s -> withNameHints (bifoldMap pure mempty pat) $ \ns -> do
      let inst = instantiatePattern (pure . fromName) ns
      parens `above` absPrec $
        "\\" <> prettyAnnotation p (prettyPattern ns $ inst <$> pat) <> "." <+>
          associate absPrec (prettyM $ inst s)
    App e1 p e2 -> prettyApp (prettyM e1) (prettyAnnotation p $ prettyM e2)
    Let (LetRec defs) scope -> parens `above` letPrec $ withNameHints ((\(LetBinding _ h _) -> h) <$> defs) $ \ns ->
      let go = ifor defs $ \i (LetBinding _ _ cl) ->
            prettyNamed
              (prettyM $ ns Vector.! i)
              (instantiateConstantDef (pure . fromName . (ns Vector.!) . unLetVar) cl)
       in "let" <+> align (vcat go)
        <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns scope)
    Case e (Branches brs) -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <$$> indent 2 (vcat $ prettyBranch <$> brs)
    ExternCode c -> prettyM c
    Wildcard -> "_"
    SourceLoc _ e -> prettyM e
    where
      prettyBranch (Branch _ pat br) = withNameHints (bifoldMap pure mempty pat) $ \ns -> do
        let inst = instantiatePattern (pure . fromName) ns
        prettyPattern ns (inst <$> pat) <+> "->" <+> prettyM (inst br)

return []

deriveEq ''Expr
deriveEq1 ''Expr
deriveShow1 ''Expr
instance (Eq1 expr, Monad expr) => Eq1 (LetRec expr) where
  liftEq = $(makeLiftEq ''LetRec)
instance (Show1 expr, Monad expr) => Show1 (LetRec expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LetRec)
instance (Eq1 expr, Monad expr) => Eq1 (LetBinding expr) where
  liftEq = $(makeLiftEq ''LetBinding)
instance (Show1 expr, Monad expr) => Show1 (LetBinding expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''LetBinding)
instance (Eq1 expr, Monad expr) => Eq1 (Branches expr) where
  liftEq = $(makeLiftEq ''Branches)
instance (Show1 expr, Monad expr) => Show1 (Branches expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Branches)
instance (Eq1 expr, Monad expr) => Eq1 (Branch expr) where
  liftEq = $(makeLiftEq ''Branch)
instance (Show1 expr, Monad expr) => Show1 (Branch expr) where
  liftShowsPrec = $(makeLiftShowsPrec ''Branch)
