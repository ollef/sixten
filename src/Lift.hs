{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Lift where
import qualified Bound.Scope.Simple as Simple
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import Data.Void

import Syntax
import qualified Syntax.Converted as Converted
import qualified Syntax.Lifted as Lifted
import Util

data LiftState = LiftState
  { freshNames :: [Name]
  , liftedFunctions :: [(Name, Lifted.Function Void)]
  }

newtype Lift a = Lift { unLifted :: State LiftState a }
  deriving (Functor, Applicative, Monad, MonadState LiftState)

liftFunction :: Lifted.Function Void -> Lift Name
liftFunction f = do
  name:names <- gets freshNames
  modify $ \s -> s
    { freshNames = names
    , liftedFunctions = (name, f) : liftedFunctions s
    }
  return name

liftExpr
  :: Converted.Expr v
  -> Lift (Lifted.Expr v)
liftExpr expr = case expr of
  Converted.Var v -> return $ Lifted.Var v
  Converted.Global g -> return $ Lifted.Global g
  Converted.Lit l -> return $ Lifted.Lit l
  Converted.Con c es -> Lifted.Con c <$> mapM liftSExpr es
  Converted.Lams d tele s -> do
    s' <- underScope liftSExpr s
    f <- liftFunction $ Lifted.Function d (teleNamedAnnotations tele) s'
    return $ Lifted.Global f
  Converted.Call retDir e es -> Lifted.Call retDir
    <$> liftExpr e
    <*> mapM (bitraverse liftSExpr pure) es
  Converted.Let h e (Simple.Scope s) -> Lifted.Let h
    <$> liftSExpr e
    <*> fmap Simple.Scope (liftExpr s)
  Converted.Case e brs -> Lifted.Case <$> liftSExpr e <*> liftBranches brs
  Converted.Prim p -> Lifted.Prim <$> mapM liftExpr p

underScope
  :: Functor m
  => (e (Var b v) -> m (e' (Var b v)))
  -> Simple.Scope b e v
  -> m (Simple.Scope b e' v)
underScope f (Simple.Scope s) = Simple.Scope <$> f s

liftSExpr
  :: Converted.SExpr v
  -> Lift (Lifted.SExpr v)
liftSExpr (Converted.Sized sz expr)
  = Lifted.Sized <$> liftExpr sz <*> liftExpr expr

liftBranches
  :: SimpleBranches QConstr Converted.Expr v
  -> Lift (SimpleBranches QConstr Lifted.Expr v)
liftBranches (SimpleConBranches cbrs) = SimpleConBranches <$> sequence
  [ (,,) qc <$> liftTelescope tele <*> underScope liftExpr s
  | (qc, tele, s) <- cbrs
  ]
liftBranches (SimpleLitBranches lbrs def) = SimpleLitBranches <$> sequence
  [ (,) l <$> liftExpr e
  | (l, e) <- lbrs
  ] <*> liftExpr def

liftTelescope
  :: Telescope Simple.Scope () Converted.Expr v
  -> Lift (Telescope Simple.Scope () Lifted.Expr v)
liftTelescope (Telescope tele) = Telescope
  <$> mapM (\(h, (), s) -> (,,) h () <$> underScope liftExpr s) tele

liftDefinitionM
  :: Converted.SExpr Void
  -> Lift (Lifted.Definition Void)
liftDefinitionM (Converted.Sized _ (Converted.Lams retDir tele s))
  = Lifted.FunctionDef . Lifted.Function retDir (teleNamedAnnotations tele)
    <$> underScope liftSExpr s
liftDefinitionM sexpr
  = Lifted.ConstantDef . Lifted.Constant (Converted.sExprDir sexpr)
    <$> liftSExpr sexpr

liftDefinition
  :: Name
  -> Converted.SExpr Void
  -> (Lifted.Definition Void, [(Name, Lifted.Function Void)])
liftDefinition name expr
  = second liftedFunctions
  $ runState (unLifted $ liftDefinitionM expr) LiftState
  { freshNames = [name <> "-lifted" <> if n == 0 then "" else shower n | n <- [(0 :: Int)..]]
  , liftedFunctions = mempty
  }
