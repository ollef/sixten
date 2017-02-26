{-# LANGUAGE GeneralizedNewtypeDeriving, MonadComprehensions, OverloadedStrings #-}
module Backend.Lift where
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Monoid
import Data.Void

import Syntax
import qualified Syntax.Sized.Converted as Converted
import qualified Syntax.Sized.Lifted as Lifted
import Util

data LiftState = LiftState
  { freshNames :: [Name]
  , liftedFunctions :: [(Name, Lifted.Function ClosureDir (Lifted.Expr ClosureDir) Void)]
  }

newtype Lift a = Lift { unLifted :: State LiftState a }
  deriving (Functor, Applicative, Monad, MonadState LiftState)

liftFunction :: Lifted.Function ClosureDir (Lifted.Expr ClosureDir) Void -> Lift Name
liftFunction f = do
  name:names <- gets freshNames
  modify $ \s -> s
    { freshNames = names
    , liftedFunctions = (name, f) : liftedFunctions s
    }
  return name

liftExpr
  :: Converted.Expr v
  -> Lift (Lifted.Expr ClosureDir v)
liftExpr expr = case expr of
  Converted.Var v -> return $ Lifted.Var v
  Converted.Global g -> return $ Lifted.Global g
  Converted.Lit l -> return $ Lifted.Lit l
  Converted.Con c es -> Lifted.Con c <$> mapM liftExpr es
  Converted.Lams d tele s -> do
    s' <- underScope liftExpr s
    tele' <- liftTelescope tele
    f <- liftFunction $ Lifted.Function d tele' s'
    return $ Lifted.Global f
  Converted.Call retDir e es -> Lifted.Call retDir
    <$> liftExpr e
    <*> mapM (bitraverse liftExpr pure) es
  Converted.Let h e s -> Lifted.Let h
    <$> liftExpr e
    <*> fmap toScope (liftExpr $ fromScope s)
  Converted.Case e brs -> Lifted.Case <$> liftExpr e <*> liftBranches brs
  Converted.Prim p -> Lifted.Prim <$> mapM liftExpr p
  Converted.Anno e t -> Lifted.Anno <$> liftExpr e <*> liftExpr t

underScope
  :: (Functor m, Monad e, Monad e')
  => (e (Var b v) -> m (e' (Var b v)))
  -> Scope b e v
  -> m (Scope b e' v)
underScope f s = toScope <$> f (fromScope s)

liftBranches
  :: Branches QConstr () Converted.Expr v
  -> Lift (Branches QConstr () (Lifted.Expr ClosureDir) v)
liftBranches (ConBranches cbrs) = ConBranches <$> sequence
  [ (,,) qc <$> liftTelescope tele <*> underScope liftExpr s
  | (qc, tele, s) <- cbrs
  ]
liftBranches (LitBranches lbrs def) = LitBranches <$> sequence
  [ (,) l <$> liftExpr e
  | (l, e) <- lbrs
  ] <*> liftExpr def
liftBranches (NoBranches sz) = NoBranches <$> liftExpr sz

liftTelescope
  :: Telescope d Converted.Expr v
  -> Lift (Telescope d (Lifted.Expr ClosureDir) v)
liftTelescope (Telescope tele) = Telescope
  <$> mapM (\(h, d, s) -> (,,) h d <$> underScope liftExpr s) tele

liftDefinitionM
  :: Converted.Expr Void
  -> Lift (Lifted.Definition ClosureDir (Lifted.Expr ClosureDir) Void)
liftDefinitionM (Converted.Anno (Converted.Lams retDir tele s) _) = do
  tele' <- liftTelescope tele
  s' <- underScope liftExpr s
  return $ Lifted.FunctionDef Public $ Lifted.Function retDir tele' s'
liftDefinitionM sexpr
  = Lifted.ConstantDef Public . Lifted.Constant (Converted.sExprDir sexpr)
    <$> liftExpr sexpr

liftDefinition
  :: Name
  -> Converted.Expr Void
  -> (Lifted.Definition ClosureDir (Lifted.Expr ClosureDir) Void, [(Name, Lifted.Function ClosureDir (Lifted.Expr ClosureDir) Void)])
liftDefinition name expr
  = second liftedFunctions
  $ runState (unLifted $ liftDefinitionM expr) LiftState
  { freshNames = [name <> "-lifted" <> if n == 0 then "" else shower n | n <- [(0 :: Int)..]]
  , liftedFunctions = mempty
  }
