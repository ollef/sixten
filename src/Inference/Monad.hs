module Inference.Monad where

import Control.Monad.Reader

import qualified Builtin.Names as Builtin
import Inference.Meta
import Syntax
import qualified Syntax.Abstract as Abstract
import VIX

type Polytype = AbstractM
type Rhotype = AbstractM -- No top-level foralls

newtype InstUntil = InstUntil Plicitness
  deriving (Eq, Ord, Show)

shouldInst :: Plicitness -> InstUntil -> Bool
shouldInst Explicit _ = False
shouldInst _ (InstUntil Explicit) = True
shouldInst p (InstUntil p') | p == p' = False
shouldInst _ _ = True

data InferEnv = InferEnv
  { localVariables :: [MetaA]
  , inferLevel :: !Level
  }

type Infer = ReaderT InferEnv VIX

runInfer :: Infer a -> VIX a
runInfer i = runReaderT i InferEnv
  { localVariables = mempty
  , inferLevel = 1
  }

level :: Infer Level
level = asks inferLevel

enterLevel :: Infer a -> Infer a
enterLevel = local $ \e -> e { inferLevel = inferLevel e + 1 }

exists
  :: NameHint
  -> Plicitness
  -> Abstract.Expr (MetaVar Plicitness Abstract.Expr)
  -> Infer AbstractM
exists hint d typ = pure <$> (existsAtLevel hint d typ =<< level)

existsType
  :: NameHint
  -> Infer AbstractM
existsType n = exists n Explicit Builtin.Type

existsVar
  :: NameHint
  -> Plicitness
  -> AbstractM
  -> Infer AbstractM
existsVar _ Constraint typ = return $ Builtin.UnsolvedConstraint typ
existsVar h Implicit typ = exists h Implicit typ
existsVar h Explicit typ = exists h Explicit typ
