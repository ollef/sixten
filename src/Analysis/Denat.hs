{-# LANGUAGE MonadComprehensions, OverloadedStrings #-}
module Analysis.Denat where

import qualified Data.Vector as Vector

import Builtin.Names
import Syntax
import Syntax.Sized.Anno
import Syntax.Sized.SLambda

denat :: Expr v -> Expr v
denat expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Lit _ -> expr
  Con ZeroConstr _ -> Lit $ Integer 0
  Con SuccConstr xs -> App (App (global AddIntName) (Anno (Lit $ Integer 1) (global IntName))) (denatAnno $ Vector.head xs)
  Con c es -> Con c $ denatAnno <$> es
  Lam h t e -> Lam h (denat t) (hoist denat e)
  App e1 e2 -> App (denat e1) (denatAnno e2)
  Let ds s -> Let (hoist denat ds) (hoist denat s)
  Case e brs -> denatCase (denatAnno e) brs
  ExternCode c retType -> ExternCode (denatAnno <$> c) (denat retType)

denatAnno
  :: Anno Expr v
  -> Anno Expr v
denatAnno (Anno e t) = Anno (denat e) (denat t)

denatCase
  :: Anno Expr v
  -> Branches () Expr v
  -> Expr v
denatCase (Anno expr _) (ConBranches [ConBranch ZeroConstr _ztele zs, ConBranch SuccConstr _stele ss])
  = let_ mempty expr (global NatName)
  $ toScope
  $ Case (Anno (pure $ B ()) (global NatName))
    (LitBranches
      (pure (LitBranch (Integer 0) $ F <$> instantiate (error "denatCase zs") (hoist denat zs)))
      (let_
        "pred"
        (App (App (global SubIntName) (intTyped $ pure $ B ())) (intTyped $ Lit $ Integer 1))
        intType
        $ mapScope (const ()) F $ hoist denat ss
      )
    )
  where
    intTyped = (`Anno` intType)
    intType = global IntName
denatCase expr (ConBranches cbrs)
  = Case
    expr
    (ConBranches [ConBranch c (hoist denat tele) (hoist denat s) | ConBranch c tele s <- cbrs])
denatCase expr (LitBranches lbrs def)
  = Case
    expr
    (LitBranches [LitBranch l (denat br) | LitBranch l br <- lbrs] (denat def))
