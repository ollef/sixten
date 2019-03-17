module Analysis.Termination where

import Protolude

import Syntax
import Syntax.Core

-- | Does this expression _definitely_ terminate when evaluated?
terminates :: (GName -> Bool) -> Expr meta v -> Bool
terminates glob expr = case expr of
  Var _ -> True
  Meta _ _ -> False
  Global n -> glob n
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> True
  App e1 _ e2 -> terminatesWhenCalled glob e1 && terminates glob e2
  Case {} -> False
  Let ds s -> all (terminates glob) (fromScope <$> letBodies ds) && terminates glob (fromScope s)
  ExternCode {} -> False
  SourceLoc _ e -> terminates glob e

-- | Does this expression _definitely_ terminate when called (and evaluated)?
terminatesWhenCalled :: (GName -> Bool) -> Expr meta v -> Bool
terminatesWhenCalled glob expr = case expr of
  Var _ -> False
  Meta _ _ -> False
  Global _ -> False
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let ds s -> all (terminates glob) (fromScope <$> letBodies ds) && terminatesWhenCalled glob (fromScope s)
  ExternCode {} -> False
  SourceLoc _ e -> terminatesWhenCalled glob e

-- | Is it cost-free to duplicate this expression?
duplicable :: Expr meta v -> Bool
duplicable expr = case expr of
  Var _ -> True
  Meta _ _ -> False
  Global _ -> True
  Con _ -> True
  Lit _ -> True
  Pi {} -> True
  Lam {} -> False
  App {} -> False
  Case {} -> False
  Let {} -> False
  ExternCode {} -> False
  SourceLoc _ e -> duplicable e
