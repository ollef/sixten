{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, OverloadedStrings, PatternSynonyms, TemplateHaskell, TypeFamilies, ViewPatterns #-}
module Syntax.Abstract where

import Control.Monad
import Data.Bifunctor
import Data.Deriving
import Data.Foldable as Foldable
import Data.Monoid
import Data.String

import Syntax
import TypeRep(TypeRep)
import Util
import Util.Tsil

-- | Expressions with variables of type @v@.
data Expr v
  = Var v
  | Global QName
  | Con QConstr
  | Lit Literal
  | Pi !NameHint !Plicitness (Type v) (Scope1 Expr v)
  | Lam !NameHint !Plicitness (Type v) (Scope1 Expr v)
  | App (Expr v) !Plicitness (Expr v)
  | Let (LetRec Expr v) (Scope LetVar Expr v)
  | Case (Expr v) (Branches Plicitness Expr v) (Type v)
  | ExternCode (Extern (Expr v)) (Type v)
  deriving (Foldable, Functor, Traversable)

-- | Synonym for documentation purposes
type Type = Expr

-------------------------------------------------------------------------------
-- Helpers
pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

let_ :: NameHint -> Expr v -> Type v -> Scope1 Expr v -> Expr v
let_ h e t s = Let (LetRec $ pure $ LetBinding h (abstractNone e) t) (mapBound (\() -> 0) s)

apps :: Foldable t => Expr v -> t (Plicitness, Expr v) -> Expr v
apps = Foldable.foldl' (uncurry . App)

appsView :: Expr v -> (Expr v, [(Plicitness, Expr v)])
appsView = second toList . go
  where
    go (App e1 p e2) = second (`Snoc` (p, e2)) $ go e1
    go e = (e, Nil)

piView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
piView (Pi h a t s) = Just (h, a, t, s)
piView _ = Nothing

lamView :: Expr v -> Maybe (NameHint, Plicitness, Type v, Scope1 Expr v)
lamView (Lam h a t s) = Just (h, a, t, s)
lamView _ = Nothing

typeApp :: Expr v -> Expr v -> Maybe (Expr v)
typeApp (Pi _ _ _ s) e = Just $ Util.instantiate1 e s
typeApp _ _ = Nothing

typeApps :: Foldable t => Expr v -> t (Expr v) -> Maybe (Expr v)
typeApps = foldlM typeApp

usedPiView
  :: Expr v
  -> Maybe (NameHint, Plicitness, Expr v, Scope1 Expr v)
usedPiView (Pi n p e s@(unusedScope -> Nothing)) = Just (n, p, e, s)
usedPiView _ = Nothing

usedPisViewM :: Expr v -> Maybe (Telescope Plicitness Expr v, Scope TeleVar Expr v)
usedPisViewM = bindingsViewM usedPiView

telescope :: Expr v -> Telescope Plicitness Expr v
telescope (pisView -> (tele, _)) = tele

pisView :: Expr v -> (Telescope Plicitness Expr v, Scope TeleVar Expr v)
pisView = bindingsView piView

lamsViewM :: Expr v -> Maybe (Telescope Plicitness Expr v, Scope TeleVar Expr v)
lamsViewM = bindingsViewM lamView

lams :: Telescope Plicitness Expr v -> Scope TeleVar Expr v -> Expr v
lams = quantify Lam

pis :: Telescope Plicitness Expr v -> Scope TeleVar Expr v -> Expr v
pis = quantify Pi

arrow :: Plicitness -> Expr v -> Expr v -> Expr v
arrow p a b = Pi mempty p a $ Scope $ pure $ F b

quantifiedConstrTypes
  :: DataDef Type v
  -> Type v
  -> (Plicitness -> Plicitness)
  -> [ConstrDef (Type v)]
quantifiedConstrTypes (DataDef cs) typ anno = map (fmap $ pis ps) cs
  where
    ps = mapAnnotations anno $ telescope typ

prettyTypedDef
  :: (Eq v, IsString v, Pretty v)
  => PrettyM Doc
  -> Definition Expr v
  -> Expr v
  -> PrettyM Doc
prettyTypedDef name (Definition a i d) _ = prettyM a <+> prettyM i <$$> name <+> "=" <+> prettyM d
prettyTypedDef name (DataDefinition d e) t = prettyDataDef name (telescope t) d <+> "=" <+> prettyM e

-------------------------------------------------------------------------------
-- Instances
instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Con c -> Con c
    Lit l -> Lit l
    Pi h a t s -> Pi h a (bind f g t) (bound f g s)
    Lam h a t s -> Lam h a (bind f g t) (bound f g s)
    App e1 a e2 -> App (bind f g e1) a (bind f g e2)
    Let ds scope -> Let (bound f g ds) (bound f g scope)
    Case e brs retType -> Case (bind f g e) (bound f g brs) (bind f g retType)
    ExternCode c t -> ExternCode (bind f g <$> c) (bind f g t)

deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  expr >>= f = bind f Global expr

instance (Eq v, IsString v, Pretty v) => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c -> prettyM c
    Lit l -> prettyM l
    Pi _ a t (unusedScope -> Just e) -> parens `above` arrPrec $
      prettyAnnotation a (prettyM t)
      <+> "->" <+>
      associate arrPrec (prettyM e)
    (usedPisViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      prettyTeleVarTypes ns tele <+> "->" <+>
      associate arrPrec (prettyM $ instantiateTele (pure . fromName) ns s)
    Pi {} -> error "impossible prettyPrec pi"
    (lamsViewM -> Just (tele, s)) -> withTeleHints tele $ \ns ->
      parens `above` absPrec $
      "\\" <> prettyTeleVarTypes ns tele <> "." <+>
      prettyM (instantiateTele (pure . fromName) ns s)
    Lam {} -> error "impossible prettyPrec lam"
    App e1 a e2 -> prettyApp (prettyM e1) (prettyAnnotation a $ prettyM e2)
    Let ds s -> parens `above` letPrec $ withLetHints ds $ \ns ->
      "let" <+> align (prettyLet ns ds)
      <+> "in" <+> prettyM (instantiateLet (pure . fromName) ns s)
    Case e brs retType -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+> "of" <+> parens (prettyM retType)
        <$$> indent 2 (prettyM brs)
    ExternCode c t -> parens `above` annoPrec $
      prettyM c <+> ":" <+> prettyM t
