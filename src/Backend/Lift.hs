{-# LANGUAGE GeneralizedNewtypeDeriving, MonadComprehensions, OverloadedStrings #-}
module Backend.Lift where

import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import Data.Void

import Syntax
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Lifted as Lifted
import Util

data LiftState = LiftState
  { freshNames :: [Name]
  , liftedFunctions :: [(Name, Lifted.Function Lifted.Expr Void)]
  }

newtype Lift a = Lift { unLifted :: State LiftState a }
  deriving (Functor, Applicative, Monad, MonadState LiftState)

liftFunction :: Lifted.Function Lifted.Expr Void -> Lift Name
liftFunction f = do
  name:names <- gets freshNames
  modify $ \s -> s
    { freshNames = names
    , liftedFunctions = (name, f) : liftedFunctions s
    }
  return name

liftExpr
  :: Closed.Expr v
  -> Lift (Lifted.Expr v)
liftExpr expr = case expr of
  Closed.Var v -> return $ Lifted.Var v
  Closed.Global g -> return $ Lifted.Global g
  Closed.Lit l -> return $ Lifted.Lit l
  Closed.Con c es -> Lifted.Con c <$> mapM liftExpr es
  Closed.Lams tele s -> do
    s' <- transverseScope liftExpr s
    tele' <- liftTelescope tele
    f <- liftFunction $ Lifted.Function tele' s'
    return $ Lifted.Global f
  Closed.Call e es -> Lifted.Call <$> liftExpr e <*> mapM liftExpr es
  Closed.PrimCall retDir e es -> Lifted.PrimCall retDir
    <$> liftExpr e
    <*> traverse (bitraverse liftExpr pure) es
  Closed.Let h e s -> Lifted.Let h
    <$> liftExpr e
    <*> fmap toScope (liftExpr $ fromScope s)
  Closed.Case e brs -> Lifted.Case <$> liftExpr e <*> liftBranches brs
  Closed.Prim p -> Lifted.Prim <$> mapM liftExpr p
  Closed.Anno e t -> Lifted.Anno <$> liftExpr e <*> liftExpr t

liftBranches
  :: Branches QConstr () Closed.Expr v
  -> Lift (Branches QConstr () Lifted.Expr v)
liftBranches (ConBranches cbrs) = ConBranches <$> sequence
  [ (,,) qc <$> liftTelescope tele <*> transverseScope liftExpr s
  | (qc, tele, s) <- cbrs
  ]
liftBranches (LitBranches lbrs def) = LitBranches <$> sequence
  [ (,) l <$> liftExpr e
  | (l, e) <- lbrs
  ] <*> liftExpr def

liftTelescope
  :: Telescope d Closed.Expr v
  -> Lift (Telescope d Lifted.Expr v)
liftTelescope (Telescope tele) = Telescope
  <$> mapM (\(h, d, s) -> (,,) h d <$> transverseScope liftExpr s) tele

liftToDefinitionM
  :: Closed.Expr Void
  -> Lift (Lifted.Definition Lifted.Expr Void)
liftToDefinitionM (Closed.Anno (Closed.Lams tele s) _) = do
  tele' <- liftTelescope tele
  s' <- transverseScope liftExpr s
  return $ Lifted.FunctionDef Public Lifted.NonClosure $ Lifted.Function tele' s'
liftToDefinitionM sexpr
  = Lifted.ConstantDef Public . Lifted.Constant <$> liftExpr sexpr

liftToDefinition
  :: Name
  -> Closed.Expr Void
  -> (Lifted.Definition Lifted.Expr Void, [(Name, Lifted.Function Lifted.Expr Void)])
liftToDefinition name expr
  = second liftedFunctions
  $ runState (unLifted $ liftToDefinitionM expr) LiftState
  { freshNames = [name <> "-lifted" <> if n == 0 then "" else shower n | n <- [(0 :: Int)..]]
  , liftedFunctions = mempty
  }

liftDefinitionM
  :: Lifted.Definition Closed.Expr Void
  -> Lift (Lifted.Definition Lifted.Expr Void)
liftDefinitionM (Lifted.FunctionDef vis cl (Lifted.Function tele s)) = do
  tele' <- liftTelescope tele
  s' <- transverseScope liftExpr s
  return $ Lifted.FunctionDef vis cl $ Lifted.Function tele' s'
liftDefinitionM (Lifted.ConstantDef vis (Lifted.Constant e)) = do
  e' <- liftExpr e
  return $ Lifted.ConstantDef vis $ Lifted.Constant e'

liftClosures
  :: Name
  -> Lifted.Definition Closed.Expr Void
  -> (Lifted.Definition Lifted.Expr Void, [(Name, Lifted.Function Lifted.Expr Void)])
liftClosures name expr
  = second liftedFunctions
  $ runState (unLifted $ liftDefinitionM expr) LiftState
  { freshNames = [name <> "-lifted-closure" <> if n == 0 then "" else shower n | n <- [(0 :: Int)..]]
  , liftedFunctions = mempty
  }
