module Inference.Monad where

import Control.Monad.Reader

import qualified Builtin.Names as Builtin
import Meta
import Syntax
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

type Witness = AbstractM

data InferEnv = InferEnv
  { constraints :: [(Witness, AbstractM)]
  , inferLevel :: !Level
  }

type Infer = ReaderT InferEnv VIX

runInfer :: Infer a -> VIX a
runInfer i = runReaderT i InferEnv
  { constraints = mempty
  , inferLevel = 1
  }

level :: Infer Level
level = asks inferLevel

enterLevel :: Infer a -> Infer a
enterLevel = local $ \e -> e { inferLevel = inferLevel e + 1 }

exists
  :: NameHint
  -> d
  -> e (MetaVar d e)
  -> Infer (MetaVar d e)
exists hint d typ = existsAtLevel hint d typ =<< level

existsType
  :: Applicative e
  => NameHint
  -> Infer (e MetaA)
existsType n = pure <$> exists n Explicit Builtin.Type

existsVar
  :: NameHint
  -> Plicitness
  -> AbstractM
  -> Infer AbstractM
existsVar _ Constraint typ = return $ Builtin.UnsolvedConstraint typ
existsVar h Implicit typ = pure <$> exists h Implicit typ
existsVar h Explicit typ = pure <$> exists h Explicit typ
