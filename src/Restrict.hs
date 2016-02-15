module Restrict where

import Syntax
import qualified Syntax.Lambda as Lambda
import qualified Syntax.LL as LL

restrictExpr :: Lambda.Expr v -> LL.Expr v
restrictExpr e = undefined

restrictDef :: Definition Lambda.Expr v -> LL.Def v
restrictDef d = undefined
