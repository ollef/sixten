{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, GADTs, OverloadedStrings, PatternSynonyms, ViewPatterns, TemplateHaskell #-}
module Syntax.Sized.Lifted where

import Control.Monad
import Data.Deriving
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Syntax hiding (Definition)
import Syntax.Sized.Anno
import TypeRep(TypeRep)
import Util

data Expr v
  = Var v
  | Global QName
  | Lit Literal
  | Con QConstr (Vector (Anno Expr v)) -- ^ Fully applied
  | Call (Expr v) (Vector (Anno Expr v)) -- ^ Fully applied, only global
  | PrimCall RetDir (Expr v) (Vector (Direction, Anno Expr v))
  | Let NameHint (Anno Expr v) (Scope1 Expr v)
  | Case (Anno Expr v) (Branches () Expr v)
  | ExternCode (Extern (Anno Expr v)) (Type v)
  deriving (Foldable, Functor, Traversable)

type Type = Expr

type FunSignature = (Telescope () Type Void, Scope TeleVar Type Void)

-------------------------------------------------------------------------------
-- Helpers

pattern MkType :: TypeRep -> Expr v
pattern MkType rep = Lit (TypeRep rep)

typeDir :: Expr v -> Direction
typeDir (MkType rep) = Direct rep
typeDir _ = Indirect

callsView :: Expr v -> Maybe (Expr v, Vector (Anno Expr v))
callsView (Call expr exprs) = Just $ go expr [exprs]
  where
    go (Call e es) ess = go e (es : ess)
    go e ess = (e, Vector.concat ess)
callsView _ = Nothing

-------------------------------------------------------------------------------
-- Instances
deriveEq1 ''Expr
deriveEq ''Expr
deriveOrd1 ''Expr
deriveOrd ''Expr
deriveShow1 ''Expr
deriveShow ''Expr

instance GlobalBind Expr where
  global = Global
  bind f g expr = case expr of
    Var v -> f v
    Global v -> g v
    Lit l -> Lit l
    Con c es -> Con c (bound f g <$> es)
    Call e es -> Call (bind f g e) (bound f g <$> es)
    PrimCall retDir e es -> PrimCall retDir (bind f g e) (fmap (bound f g) <$> es)
    Let h e s -> Let h (bound f g e) (bound f g s)
    Case e brs -> Case (bound f g e) (bound f g brs)
    ExternCode c retType -> ExternCode (bound f g <$> c) (bind f g retType)

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  expr >>= f = bind f Global expr

instance v ~ Doc => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Lit l -> prettyM l
    Con c es -> prettyApps (prettyM c) $ prettyM <$> es
    Call e es -> prettyApps (prettyM e) $ prettyM <$> es
    PrimCall retDir f es -> "primcall" <+> prettyAnnotation retDir (prettyApps (prettyM f) $ (\(d, e) -> prettyAnnotation d $ prettyM e) <$> es)
    Let h (Anno e t) s -> parens `above` letPrec $ withNameHint h $ \n ->
      "let" <+> prettyM n <+> ":" <+> prettyM t <+> "=" <+> prettyM e <+> "in" <+>
        prettyM (Util.instantiate1 (pure $ fromName n) s)
    Case e brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM e) <+>
      "of" <$$> indent 2 (prettyM brs)
    ExternCode c retType ->
      parens `above` annoPrec $ prettyM c <+> ":" <+> prettyM retType
