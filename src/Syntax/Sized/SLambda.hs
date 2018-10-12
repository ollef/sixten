{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, GADTs, MonadComprehensions, OverloadedStrings, PatternSynonyms, TemplateHaskell, ViewPatterns #-}
module Syntax.Sized.SLambda where

import Protolude hiding (Type, TypeRep)

import Data.Deriving
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Syntax
import Syntax.Sized.Anno
import TypedFreeVar
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con QConstr (Vector (Anno Expr v)) -- ^ Fully applied
  | Lam !NameHint (Type v) (AnnoScope1 Expr v)
  | App (Expr v) (Anno Expr v)
  | Let (LetRec Expr v) (Scope LetVar Expr v)
  | Case (Anno Expr v) (Branches () Expr v)
  | ExternCode (Extern (Anno Expr v)) (Type v)
  deriving (Foldable, Functor, Traversable)

type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

lam :: FreeVar d e -> Type (FreeVar d e) -> Anno Expr (FreeVar d e) -> Expr (FreeVar d e)
lam v t = Lam (varHint v) t . abstract1Anno v

letRec :: Vector (FreeVar d e, Anno Expr (FreeVar d e)) -> Expr (FreeVar d e) -> Expr (FreeVar d e)
letRec ds expr = do
  let ds' = [LetBinding (varHint v) (noSourceLoc "SLambda") (abstr e) t | (v, Anno e t) <- ds]
  Let (LetRec ds') $ abstr expr
  where
    abstr = abstract $ letAbstraction $ fst <$> ds

appsView :: Expr v -> (Expr v, Vector (Anno Expr v))
appsView = go []
  where
    go args (App e1 e2) = go (e2:args) e1
    go args e = (e, Vector.fromList args)

lamView :: Expr v -> Maybe (NameHint, (), Expr v, AnnoScope () Expr v)
lamView (Lam h e s) = Just (h, (), e, s)
lamView _ = Nothing

let_ :: NameHint -> Expr v -> Type v -> Scope1 Expr v -> Expr v
let_ h e t s = Let (LetRec $ pure $ LetBinding h (noSourceLoc "SLambda") (abstractNone e) t) (mapBound (\() -> 0) s)

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
  expr >>= f = case expr of
    Var v -> f v
    Global v -> Global v
    Lit l -> Lit l
    Con qc es -> Con qc ((>>>= f) <$> es)
    Lam h e s -> Lam h (e >>= f) (s >>>= f)
    App e1 e2 -> App (e1 >>= f) (e2 >>>= f)
    Let ds s -> Let (ds >>>= f) (s >>>= f)
    Case e brs -> Case (e >>>= f) (brs >>>= f)
    ExternCode c retType -> ExternCode ((>>>= f) <$> c) (retType >>= f)

pattern Lams :: Telescope () Expr v -> AnnoScope TeleVar Expr v -> Expr v
pattern Lams tele s <- (annoBindingsViewM lamView -> Just (tele, s))

instance GBind Expr where
  global = Global
  gbind f expr = case expr of
    Var _ -> expr
    Global v -> f v
    Lit _ -> expr
    Con qc es -> Con qc (gbound f <$> es)
    Lam h e s -> Lam h (gbind f e) (gbound f s)
    App e1 e2 -> App (gbind f e1) (gbound f e2)
    Let ds s -> Let (gbound f ds) (gbound f s)
    Case e brs -> Case (gbound f e) (gbound f brs)
    ExternCode c retType -> ExternCode (gbound f <$> c) (gbind f retType)

instance v ~ Doc => Pretty (Expr v) where
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
    (annoBindingsViewM lamView -> Just (tele, s)) -> parens `above` absPrec $
      withTeleHints tele $ \ns ->
        "\\" <> prettyTeleVarTypes ns tele <> "." <+>
        associate absPrec (prettyM $ instantiateAnnoTele (pure . fromName) ns s)
    Lam {} -> panic "impossible prettyPrec lam"
    ExternCode c retType -> parens `above` annoPrec $ prettyM c <+> ":" <+> prettyM retType
