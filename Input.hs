{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Input where

import Bound
import Control.Monad
import Data.Bitraversable
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.Map(Map)
import Data.Monoid
import Data.String
import Prelude.Extras

import Annotation
import Branches
import Data
import Hint
import Util
import Pretty

data Expr v
  = Var v
  | Con Constr
  | Type                                      -- ^ Type : Type
  | Pi  !NameHint !Plicitness (Type v) (Scope1 Expr v) -- ^ Dependent function space
  | Lam !NameHint !Plicitness (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Case (Expr v) (Branches Expr v)
  | Anno (Expr v) (Expr v)
  | Wildcard                         -- ^ Attempt to infer it
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-- * Smart constructors
lam :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
lam x p Nothing  = Lam x p
lam x p (Just t) = (`Anno` Pi x p t (Scope Wildcard)) . Lam x p

piType :: NameHint -> Plicitness -> Maybe (Type v) -> Scope1 Expr v -> Expr v
piType x p Nothing  = Pi x p Wildcard
piType x p (Just t) = Pi x p t

anno :: Expr v -> Expr v -> Expr v
anno e Wildcard = e
anno e t        = Anno e t

-- TODO move to parse?
-- | A definition or type declaration on the top-level
data TopLevelParsed v
  = ParsedDefLine  (Maybe v) (Expr v) -- ^ Maybe v means that we can use wildcard names that refer e.g. to the previous top-level thing
  | ParsedTypeDecl v         (Type v)
  | ParsedData  v (DataDef Type v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

-- TODO Move this and Program to its own module
data Definition expr v
  = Definition (expr v)
  | DataDefinition (DataDef expr v)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty (expr v) => Pretty (Definition expr v) where
  prettyM (Definition d) = prettyM d
  prettyM (DataDefinition d) = prettyM d

type Program v = Map v (Definition Expr v, Type v)

abstractDef :: Monad expr
            => (a -> Maybe b) -> Definition expr a -> Definition expr (Var b a)
abstractDef f (Definition d) = Definition $ fromScope $ abstract f d
abstractDef f (DataDefinition d) = DataDefinition $ abstractDataDef f d

instantiateDef :: (b -> expr a) -> Definition expr (Var b a) -> Definition expr a
instantiateDef = undefined

bitraverseDef :: (Applicative f, Bitraversable expr)
              => (a -> f a')
              -> (b -> f b')
              -> Definition (expr a) b
              -> f (Definition (expr a') b')
bitraverseDef f g (Definition d) = Definition <$> bitraverse f g d
bitraverseDef f g (DataDefinition d) = DataDefinition <$> bitraverseDataDef f g d

recursiveAbstractDefs :: (Eq v, Monad f, Functor t, Foldable t, Hashable v)
                      => t (v, Definition f v) -> t (Definition f (Var Int v))
recursiveAbstractDefs es = (abstractDef (`HM.lookup` vs) . snd) <$> es
  where
    vs = HM.fromList $ zip (toList $ fst <$> es) [(0 :: Int)..]

-------------------------------------------------------------------------------
-- * Views
piView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
piView (Pi n p e s) = Just (n, p, e, s)
piView _            = Nothing

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
    Con c       -> Con c
    Type        -> Type
    Pi  n p t s -> Pi n p (t >>= f) (s >>>= f)
    Lam n p s   -> Lam n p (s >>>= f)
    App e1 p e2 -> App (e1 >>= f) p (e2 >>= f)
    Case e brs  -> Case (e >>= f) (brs >>>= f)
    Anno e t    -> Anno (e >>= f) (t >>= f)
    Wildcard    -> Wildcard

instance (IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v     -> prettyM v
    Con c     -> prettyM c
    Type      -> pure $ text "Type"
    Pi  h p Wildcard s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "forall" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
      <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    Pi  h p t s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "forall" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
      <+> prettyM ":" <+> inviolable (prettyM t)
      <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    Lam h p s -> withNameHint h $ \x -> parens `above` absPrec $
      prettyM "\\" <+> inviolable (braces `iff` (p == Implicit) $ prettyM x)
        <> prettyM "." <+> associate  (prettyM $ instantiate1 (pure $ fromText x) s)
    App e1 p e2 -> prettyApp (prettyM e1) (braces `iff` (p == Implicit) $ prettyM e2)
    Case e brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM e) <+> prettyM "of" <$$> prettyM brs
    Anno e t  -> parens `above` annoPrec $
      prettyM e <+> prettyM ":" <+> associate (prettyM t)
    Wildcard  -> pure $ text "_"
