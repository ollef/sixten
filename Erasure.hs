module Erasure where
import Bound

import Annotation
import Branches
import qualified Core
import Data
import Definition
import qualified Lambda

type Core = Core.Expr
type Lambda = Lambda.Expr

erase :: HasRelevance a => Core a v -> Lambda v
erase expr = case expr of
  Core.Var v -> Lambda.Var v
  Core.Global g -> Lambda.Global g
  Core.Con c -> Lambda.Con c
  Core.Type -> error "erasure type"
  Core.Pi _ _ _ s -> erase $ instantiate1 (error "erasure pi") s
  Core.Lam h a _ s -> case relevance a of
    Irrelevant -> erase $ instantiate1 (error "erasure lambda") s
    Relevant -> Lambda.etaLam h $ toScope $ erase $ fromScope s
  Core.App e1 a e2 -> case relevance a of
    Irrelevant -> erase e1
    Relevant -> Lambda.App (erase e1) (erase e2)
  Core.Case e brs -> Lambda.Case (erase e) (eraseBranches brs)
  where
    eraseBranches (ConBranches cbrs) = ConBranches [(c, hs, toScope $ erase $ fromScope s)  | (c, hs, s) <- cbrs]
    eraseBranches (LitBranches lbrs d) = LitBranches [(l, erase e) | (l, e) <- lbrs] (erase d)

eraseDef :: HasRelevance a => Definition (Core a) v -> Definition Lambda v
eraseDef (Definition e) = Definition $ erase e
eraseDef (DataDefinition DataDef {})
  = DataDefinition $ DataDef mempty mempty
