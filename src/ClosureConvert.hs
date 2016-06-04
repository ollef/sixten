{-# LANGUAGE RecursiveDo #-}
module ClosureConvert where

import qualified Bound.Scope.Simple as Simple
import Control.Applicative
import Control.Monad.Except
import Data.String
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import qualified Builtin
import Meta
import Syntax
import Syntax.Lifted
import TCM
import Util

data VarInfo a = Unknown
  deriving Show

instance Show1 VarInfo

type Meta = MetaVar VarInfo
type LiftedM e s = Lifted e (Meta s)

type ExprM s = Expr (Meta s)
type StmtM s = Stmt (Meta s)
type LBodyM s = Lifted Body (Meta s)
type OperandM s = Operand (Meta s)

convertExpr :: LiftedM Stmt s -> ExprM s -> TCM s (LiftedM Stmt s)
convertExpr sz expr = do
  trp "convertExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Operand o -> convertOperand sz o
    Con qc os -> conLStmt sz qc <$> forM os (\(o, sz') -> do
      sze <- convertOperand (lLit 1) sz'
      oe <- convertOperand sze o
      return (oe, sze)
     )
    Call o os -> convertCall sz o os
  modifyIndent pred
  trp "convertExpr res" $ show <$> result
  return result

convertStmt :: StmtM s -> TCM s (LiftedM Stmt s)
convertStmt expr = case expr of
  Sized sz e -> do
    liftedSz <- convertOperand (lLit 1) sz
    convertExpr liftedSz e
  Let h e s -> do
    v <- forall_ h Unknown
    e' <- convertStmt e
    s' <- convertStmt $ instantiateVar (\() -> v) s
    return $ letLStmt h e' $ Simple.abstract1 v s'
  Case (o, osz) brs -> do
    liftedSz <- convertOperand (lLit 1) osz
    liftedO <- convertOperand liftedSz o
    caseLStmt (liftedO, liftedSz) <$> convertBranches brs

convertOperand :: LiftedM Stmt s -> OperandM s -> TCM s (LiftedM Stmt s)
convertOperand sz operand = case operand of
  Local v -> return $ lSizedOperand sz $ Local v
  Global _ -> convertCall sz operand mempty
  Lit l -> return $ lLit l

convertCall
  :: LiftedM Stmt s
  -> OperandM s
  -> Vector (OperandM s)
  -> TCM s (LiftedM Stmt s)
convertCall sz operand args = case operand of
  Local _ -> return
           $ lSizedInnerExpr sz
           $ Call (Global $ Builtin.apply argsLen)
                  (Vector.cons operand args)
  Global g -> known g =<< relevantDefArity g
  Lit _ -> throwError "convertCall: Lit"
  where
    argsLen = Vector.length args
    todo = Global $ fromString "convertCall-TODO"
    known g arity
      | argsLen < arity
        = return $ singleLifted mempty
        ( Function Direct (Vector.replicate (1 + arity - argsLen) (mempty, Indirect)) -- TODO direction
        $ Simple.toScope
        $ Case (Local $ B 0, todo)
        $ SimpleConBranches
          [( Builtin.Closure
          , SimpleTelescope $ Vector.replicate (arity + 2)
          (mempty, Simple.Scope $ Sized todo $ Operand $ Lit 0)
          -- TODO lift the size?
          , Simple.toScope $ Sized todo
                    $ Call (Global g)
                    $ Local . B <$> Vector.enumFromN 2 argsLen
                   <|> Local . F . B <$> Vector.enumFromN 1 (arity - argsLen)
          )]
        )
        $ Simple.Scope $ Sized todo
        $ Con Builtin.Closure
        $ Vector.cons (Local $ B (), Lit 1)
        $ Vector.cons (Lit $ fromIntegral $ arity - argsLen, Lit 1)
        $ (\x -> (fmap F x, Lit 1)) <$> args
      | argsLen > arity = do
        let (args', rest) = Vector.splitAt argsLen args
        return $ letLStmt mempty (pureLifted $ Sized (Lit 1) $ Call (Global g) args')
               $ Simple.toScope
               $ lSizedInnerExpr (F <$> sz)
               $ Call (Global $ Builtin.apply $ Vector.length args')
                      (Vector.cons (Local $ B ()) $ fmap F <$> rest)
      | otherwise = return $ lSizedInnerExpr sz $ Call (Global g) args

convertBranches
  :: SimpleBranches QConstr Stmt (Meta s)
  -> TCM s (LBranches (Meta s))
convertBranches (SimpleConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMSimpleTele tele $ \h s -> do
      let t = instantiateSimpleTeleVars vs s
      t' <- convertStmt t
      v <- forall_ h Unknown
      return (v, (h, Simple.Scope $ abstr <$> t'))
    let vs = fst <$> tele'
        abstr x = maybe (F x) B $ teleAbstraction vs x
    brScope' <- convertStmt $ instantiateSimpleTeleVars vs brScope
    return (c, snd <$> tele', Simple.Scope $ abstr <$> brScope')
  return $ conLStmtBranches cbrs'
convertBranches (SimpleLitBranches lbrs def)
  = litLStmtBranches <$> sequence [(,) l <$> convertStmt e | (l, e) <- lbrs]
                     <*> convertStmt def

convertBody :: Body (MetaVar VarInfo s) -> TCM s (LBody (MetaVar VarInfo s))
convertBody (ConstantBody (Constant d e))
  = mapLifted (ConstantBody . Constant d) <$> convertStmt e
convertBody (FunctionBody (Function d xs s)) = do
  trp "convertBody fun" $ show <$> Simple.fromScope s
  modifyIndent succ
  vars <- mapM ((`forall_` Unknown) . fst) xs
  let e = instantiateVar ((vars Vector.!) . unTele) s
      abstr = unvar (const Nothing) (fmap Tele . (`Vector.elemIndex` vars))
  e' <- convertStmt e
  let result = mapLifted (FunctionBody . Function d xs . Simple.abstract abstr) e'
  modifyIndent pred
  trs "convertBody res" vars
  trp "convertBody res" $ show <$> e'
  return result
