module Erasure where

import Data.Maybe
import qualified Data.Vector as Vector

import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Lambda as Lambda

type Abstract = Abstract.Expr
type Lambda = Lambda.Expr

erase :: HasRelevance a => Abstract a v -> Lambda v
erase expr = case expr of
  Abstract.Var v -> Lambda.Var v
  Abstract.Global g -> Lambda.Global g
  Abstract.Con c -> Lambda.Con c
  Abstract.Lit l -> Lambda.Lit l
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
    eraseTele tele@(Telescope v) =
        ( permFun
        , Telescope $ Vector.map (\(h, _, s) -> (h, (), eraseScope $ mapBound permFun s))
        $ Vector.filter (\(_, p, _) -> isRelevant p) v
        )
      where
        permFun (Tele n) = Tele $ fromMaybe (error "erasure tele") $ perm Vector.! n
        perm = Vector.fromList $ fst $
          Vector.foldr (\p (xs, i) -> case relevance p of
            Irrelevant -> (Nothing : xs, i)
            Relevant -> (Just i : xs, i + 1)) ([], 0) (teleAnnotations tele)
    eraseScope = toScope . erase . fromScope
    eraseBranches (ConBranches cbrs) = ConBranches [(c, tele', eraseScope $ mapBound permFun s)  | (c, tele, s) <- cbrs, let (permFun, tele') = eraseTele tele]
    eraseBranches (LitBranches lbrs d) = LitBranches [(l, erase e) | (l, e) <- lbrs] (erase d)

eraseDef :: HasRelevance a => Definition (Abstract a) v -> Definition Lambda v
eraseDef (Definition e) = Definition $ erase e
eraseDef (DataDefinition DataDef {})
  = DataDefinition $ DataDef mempty
