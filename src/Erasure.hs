module Erasure where
import Bound

import Syntax.Annotation
import Syntax.Branches
import qualified Syntax.Abstract as Abstract
import Syntax.Data
import Syntax.Definition
import qualified Syntax.Lambda as Lambda

type Abstract = Abstract.Expr
type Lambda = Lambda.Expr

erase :: HasRelevance a => Abstract a v -> Lambda v
erase expr = case expr of
  Abstract.Var v -> Lambda.Var v
  Abstract.Global g -> Lambda.Global g
  Abstract.Con c -> Lambda.Con c
  Abstract.Type -> error "erasure type"
  Abstract.Pi _ _ _ s -> erase $ instantiate1 (error "erasure pi") s
  Abstract.Lam h a _ s -> case relevance a of
    Irrelevant -> erase $ instantiate1 (error "erasure lambda") s
    Relevant -> Lambda.etaLam h $ toScope $ erase $ fromScope s
  Abstract.App e1 a e2 -> case relevance a of
    Irrelevant -> erase e1
    Relevant -> Lambda.App (erase e1) (erase e2)
  Abstract.Case e brs -> Lambda.Case (erase e) (eraseBranches brs)
  where
    eraseBranches (ConBranches cbrs) = ConBranches [(c, hs, toScope $ erase $ fromScope s)  | (c, hs, s) <- cbrs]
    eraseBranches (LitBranches lbrs d) = LitBranches [(l, erase e) | (l, e) <- lbrs] (erase d)

eraseDef :: HasRelevance a => Definition (Abstract a) v -> Definition Lambda v
eraseDef (Definition e) = Definition $ erase e
eraseDef (DataDefinition DataDef {})
  = DataDefinition $ DataDef mempty mempty
