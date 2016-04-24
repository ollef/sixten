{-# LANGUAGE RecursiveDo #-}
module ClosureConvert where

import qualified Bound.Scope.Simple as Simple
import Control.Applicative
import Control.Monad.Except
import Data.Bitraversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import qualified Builtin
import Meta
import Syntax
import Syntax.Lifted
import TCM

data VarInfo a = Unknown
  deriving Show

instance Show1 VarInfo

type Meta = MetaVar VarInfo
type LiftedM e s = Lifted e (Meta s)

type ExprM s = Expr (Meta s)
type LBodyM s = Lifted (Body Expr) (Meta s)
type OperandM s = Operand (Meta s)

convertExpr :: ExprM s -> TCM s (LiftedM Expr s)
convertExpr expr = do
  trp "convertExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Operand o -> convertOperand o
    Con qc os -> conLExpr qc <$> mapM (bitraverse convertOperand convertOperand) os
    Ref _e -> undefined
    Let h e s -> do
      v <- forall_ h Unknown
      e' <- convertExpr e
      s' <- convertExpr $ instantiate1 (pure v) s
      return $ letLExpr letExpr h e' $ Simple.abstract1 v s'
    Call o os -> convertCall o os
    Case o brs -> caseLExpr <$> convertOperand o <*> convertBranches brs
    Error -> return $ pureLifted Error
  modifyIndent pred
  trp "convertExpr res" $ show <$> result
  return result

convertOperand :: OperandM s -> TCM s (LiftedM Expr s)
convertOperand operand = case operand of
  Local v -> return $ pureLifted $ Operand $ Local v
  Global _ -> convertCall operand mempty
  Lit l -> return $ pureLifted $ Operand $ Lit l

convertCall
  :: OperandM s
  -> Vector (OperandM s)
  -> TCM s (LiftedM Expr s)
convertCall operand args = case operand of
  Local _ -> return $ pureLifted
           $ Call (Global $ Builtin.apply argsLen)
                  (Vector.cons operand args)
  Global g -> known g =<< relevantDefArity g
  Lit _ -> throwError "convertCall: Lit"
  where
    argsLen = Vector.length args
    known g arity
      | argsLen < arity
        = return $ singleLifted mempty
        ( Function (Vector.replicate (1 + arity - argsLen) mempty)
        $ toScope $ Case (Local $ B 0)
        $ ConBranches
          [( Builtin.closure
          , Telescope $ Vector.replicate (arity + 2)
          (mempty, ReEx, Scope $ Operand $ Lit 0)
          , toScope $ Call (Global g)
                    $ Local . B <$> Vector.enumFromN 2 argsLen
                   <|> Local . F . B <$> Vector.enumFromN 1 (arity - argsLen)
          )] $ Operand $ Lit 0
        )
        $ Simple.Scope $ Con Builtin.closure
        $ Vector.cons (Local $ B (), Lit 1)
        $ Vector.cons (Lit $ fromIntegral $ arity - argsLen, Lit 1)
        $ (\x -> (fmap F x, Lit 1)) <$> args
      | argsLen > arity = do
        let (args', rest) = Vector.splitAt argsLen args
        return $ pureLifted
               $ letExpr mempty (Call (Global g) args') $ toScope
               $ Call (Global $ Builtin.apply $ Vector.length args')
                      (Vector.cons (Local $ B ()) $ fmap F <$> rest)
      | otherwise = return $ pureLifted $ Call (Global g) args

convertBranches
  :: Branches QConstr Expr (Meta s)
  -> TCM s (Lifted (Branches QConstr Expr) (Meta s))
convertBranches (ConBranches cbrs _) = do
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h a s -> do
      let t = instantiateTele pureVs s
      t' <- convertExpr t
      v <- forall_ h Unknown
      return (v, (h, a, t' >>>= (\x -> pure . maybe (F x) B $ abstr x)))
    let vs = fst <$> tele'
        abstr = teleAbstraction vs
        pureVs = pure <$> vs
    brScope' <- convertExpr $ instantiateTele pureVs brScope
    return (c, snd <$> tele', brScope' >>>= (\x -> pure . maybe (F x) B $ abstr x))
  return $ conLExprBranches cbrs' (Operand $ Lit 0)

convertBranches (LitBranches lbrs def)
  = litLExprBranches <$> sequence [(,) l <$> convertExpr e | (l, e) <- lbrs]
                     <*> convertExpr def

convertBody :: Body Expr (MetaVar VarInfo s) -> TCM s (LBody (MetaVar VarInfo s))
convertBody (Constant e) = mapLifted Constant <$> convertExpr e
convertBody (Function xs s) = do
  trp "convertBody fun" $ show <$> fromScope s
  modifyIndent succ
  vars <- mapM (`forall_` Unknown) xs
  let e = instantiate (pure . (vars Vector.!) . unTele) s
      abstr = unvar (const Nothing) (fmap Tele . (`Vector.elemIndex` vars))
  e' <- convertExpr e
  let result = mapLifted (Function xs . abstract abstr) e'
  modifyIndent pred
  trs "convertBody res" vars
  trp "convertBody res" $ show <$> e'
  return result
