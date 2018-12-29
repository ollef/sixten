{-# LANGUAGE MonadComprehensions, OverloadedStrings #-}
module Analysis.Denat where

import Protolude

import qualified Data.Vector as Vector

import Builtin.Names
import Syntax
import Syntax.Sized.Anno
import Syntax.Sized.SLambda

denat :: Expr v -> Expr v
denat expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Lit l -> Lit $ denatLit l
  Con ZeroConstr _ -> Lit $ Integer 0
  Con SuccConstr xs -> succInt $ denatAnno $ Vector.head xs
  Con c es -> Con c $ denatAnno <$> es
  Lam h t e -> Lam h (denat t) (hoist denat e)
  App e1 e2 -> App (denat e1) (denatAnno e2)
  Let ds s -> Let (hoist denat ds) (hoist denat s)
  Case e brs -> denatCase (denatAnno e) brs
  ExternCode c retType -> ExternCode (denatAnno <$> c) (denat retType)

denatLit :: Literal -> Literal
denatLit l@Integer {} = l
denatLit (Natural n) = Integer $ fromIntegral n
denatLit l@Byte {} = l
denatLit l@TypeRep {} = l

succInt :: Anno Expr v -> Expr v
succInt (Anno (Lit (Integer n)) _) = Lit $ Integer $! n + 1
succInt expr = App (App (global $ gname AddIntName) (Anno (Lit $ Integer 1) (global $ gname IntName))) expr

denatAnno
  :: Anno Expr v
  -> Anno Expr v
denatAnno (Anno e t) = Anno (denat e) (denat t)

denatCase
  :: Anno Expr v
  -> Branches () Expr v
  -> Expr v
denatCase (Anno expr _) (ConBranches [ConBranch ZeroConstr _ztele zs, ConBranch SuccConstr _stele ss])
  = let_ mempty expr (global $ gname NatName)
  $ toScope
  $ Case (Anno (pure $ B ()) (global $ gname NatName))
    (LitBranches
      (pure (LitBranch (Integer 0) $ F <$> instantiate (panic "denatCase zs") (hoist denat zs)))
      (let_
        "pred"
        (App (App (global $ gname SubIntName) (intTyped $ pure $ B ())) (intTyped $ Lit $ Integer 1))
        intType
        $ mapScope (const ()) F $ hoist denat ss
      )
    )
  where
    intTyped = (`Anno` intType)
    intType = global $ gname IntName
denatCase expr (ConBranches cbrs)
  = Case
    expr
    (ConBranches [ConBranch c (hoist denat tele) (hoist denat s) | ConBranch c tele s <- cbrs])
denatCase expr (LitBranches lbrs def)
  = Case
    expr
    (LitBranches [LitBranch (denatLit l) (denat br) | LitBranch l br <- lbrs] (denat def))
