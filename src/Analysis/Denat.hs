{-# LANGUAGE MonadComprehensions, OverloadedStrings #-}
module Analysis.Denat where

import qualified Data.Vector as Vector

import Builtin
import Syntax
import Syntax.Sized.SLambda

denat :: Expr v -> Expr v
denat expr = case expr of
  Var _ -> expr
  Global _ -> expr
  Lit _ -> expr
  Con ZeroConstr _ -> Lit $ Integer 0
  Con SuccConstr xs -> App (App (global AddIntName) (Lit $ Integer 1)) (denat $ Vector.head xs)
  Con c es -> Con c $ denat <$> es
  Lam h t e -> Lam h (denat t) (hoist denat e)
  App e1 e2 -> App (denat e1) (denat e2)
  Let h e t s -> Let h (denat e) (denat t) (hoist denat s)
  Case e brs -> denatCase (denat e) brs
  Anno e t -> Anno (denat e) (denat t)

denatCase
  :: Expr v
  -> Branches QConstr () Expr v
  -> Expr v
denatCase expr (ConBranches [(ZeroConstr, _ztele, zs), (SuccConstr, _stele, ss)])
  = Let mempty expr (global NatName)
  $ toScope
  $ Case (pure $ B ())
    (LitBranches
      (pure (Integer 0, F <$> instantiate (error "denatCase zs") (hoist denat zs)))
      (Let "pred" (App (App (global SubIntName) (pure $ B ())) (Lit $ Integer 1)) (global NatName)
      $ mapScope (const ()) F $ hoist denat ss
      )
    )
denatCase expr (ConBranches cbrs)
  = Case
    expr
    (ConBranches [(c, hoist denat tele, hoist denat s) | (c, tele, s) <- cbrs])
denatCase expr (LitBranches lbrs def)
  = Case
    expr
    (LitBranches [(l, denat br) | (l, br) <- lbrs] (denat def))
