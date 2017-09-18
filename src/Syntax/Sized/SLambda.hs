{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, OverloadedStrings, PatternSynonyms, TemplateHaskell, ViewPatterns #-}
module Syntax.Sized.SLambda where

import Control.Monad
import Data.Deriving
import Data.Monoid
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax hiding (lamView)
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con QConstr (Vector (Expr v)) -- ^ Fully applied
  | Lam !NameHint (Type v) (Scope1 Expr v)
  | App (Expr v) (Expr v)
  | Let (LetRec Expr v) (Scope LetVar Expr v)
  | Case (Expr v) (Branches QConstr () Expr v)
  | Anno (Expr v) (Type v)
  | ExternCode (Extern (Expr v))
  deriving (Foldable, Functor, Traversable)

type Type = Expr

appsView :: Expr v -> (Expr v, Vector (Expr v))
appsView = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args e = (e, Vector.fromList args)

lamView :: Expr v -> Maybe (NameHint, (), Expr v, Scope () Expr v)
lamView (Anno e _) = lamView e
lamView (Lam h e s) = Just (h, (), e, s)
lamView _ = Nothing

let_ :: NameHint -> Expr v -> Type v -> Scope1 Expr v -> Expr v
let_ h e t s = Let (LetRec $ pure $ LetBinding h (abstractNone e) t) (mapBound (\() -> 0) s)

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = bind f Global expr

pattern Lams :: Telescope () Expr v -> Scope TeleVar Expr v -> Expr v
pattern Lams tele s <- (bindingsViewM lamView -> Just (tele, s))

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con qc es -> Con qc (bind f g <$> es)
    Lam h e s -> Lam h (bind f g e) (bound f g s)
    App e1 e2 -> App (bind f g e1) (bind f g e2)
    Let ds s -> Let (bound f g ds) (bound f g s)
    Case e brs -> Case (bind f g e) (bound f g brs)
    Anno e t -> Anno (bind f g e) (bind f g t)
    ExternCode c -> ExternCode (bind f g <$> c)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Lit l -> prettyM l
    App e1 e2 -> prettyApp (prettyM e1) (prettyM e2)
    Let ds s -> parens `above` letPrec $ withLetHints ds $ \ns ->
      "let" <+> align (prettyLet ns ds)
      <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    Anno e t -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM t
    (bindingsViewM lamView -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettyTeleVarTypes ns tele <> "." <+>
        associate absPrec (prettyM $ instantiateTele (pure . fromName) ns s)
    Lam {} -> error "impossible prettyPrec lam"
    ExternCode c -> prettyM c
