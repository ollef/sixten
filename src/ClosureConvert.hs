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

type InnerExprM s = InnerExpr (Meta s)
type ExprM s = Expr (Meta s)
type LBodyM s = Lifted (Body Expr) (Meta s)
type OperandM s = Operand (Meta s)

convertInnerExpr :: LiftedM Expr s -> InnerExprM s -> TCM s (LiftedM Expr s)
convertInnerExpr sz expr = do
  trp "convertInnerExpr" $ show <$> expr
  modifyIndent succ
  result <- case expr of
    Operand o -> convertOperand sz o
    Con qc os -> conLExpr sz qc <$> forM os (\(o, sz') -> do
      sze <- convertOperand (lLit 1) sz'
      oe <- convertOperand sze o
      return (oe, sze)
     )
    Call o os -> convertCall sz o os
  modifyIndent pred
  trp "convertInnerExpr res" $ show <$> result
  return result

convertExpr :: ExprM s -> TCM s (LiftedM Expr s)
convertExpr expr = case expr of
  Sized sz e -> do
    liftedSz <- convertOperand (lLit 1) sz
    convertInnerExpr liftedSz e
  Let h e s -> do
    v <- forall_ h Unknown
    e' <- convertExpr e
    s' <- convertExpr $ instantiateVar (\() -> v) s
    return $ letLExpr h e' $ Simple.abstract1 v s'
  Case (o, osz) brs -> do
    liftedSz <- convertOperand (lLit 1) osz
    liftedO <- convertOperand liftedSz o
    caseLExpr (liftedO, liftedSz) <$> convertBranches brs

convertOperand :: LiftedM Expr s -> OperandM s -> TCM s (LiftedM Expr s)
convertOperand sz operand = case operand of
  Local v -> return $ lSizedOperand sz $ Local v
  Global _ -> convertCall sz operand mempty
  Lit l -> return $ lLit l

convertCall
  :: LiftedM Expr s
  -> OperandM s
  -> Vector (OperandM s)
  -> TCM s (LiftedM Expr s)
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
        ( Function (Vector.replicate (1 + arity - argsLen) mempty)
        $ Simple.toScope
        $ Case (Local $ B 0, todo)
        $ SimpleConBranches
          [( Builtin.closure
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
        $ Con Builtin.closure
        $ Vector.cons (Local $ B (), Lit 1)
        $ Vector.cons (Lit $ fromIntegral $ arity - argsLen, Lit 1)
        $ (\x -> (fmap F x, Lit 1)) <$> args
      | argsLen > arity = do
        let (args', rest) = Vector.splitAt argsLen args
        return $ letLExpr mempty (pureLifted $ Sized (Lit 1) $ Call (Global g) args')
               $ Simple.toScope
               $ lSizedInnerExpr (F <$> sz)
               $ Call (Global $ Builtin.apply $ Vector.length args')
                      (Vector.cons (Local $ B ()) $ fmap F <$> rest)
      | otherwise = return $ lSizedInnerExpr sz $ Call (Global g) args

convertBranches
  :: SimpleBranches QConstr Expr (Meta s)
  -> TCM s (LBranches (Meta s))
convertBranches (SimpleConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(c, tele, brScope) -> mdo
    tele' <- forMSimpleTele tele $ \h s -> do
      let t = instantiateSimpleTeleVars vs s
      t' <- convertExpr t
      v <- forall_ h Unknown
      return (v, (h, Simple.Scope $ abstr <$> t'))
    let vs = fst <$> tele'
        abstr x = maybe (F x) B $ teleAbstraction vs x
    brScope' <- convertExpr $ instantiateSimpleTeleVars vs brScope
    return (c, snd <$> tele', Simple.Scope $ abstr <$> brScope')
  return $ conLExprBranches cbrs'
convertBranches (SimpleLitBranches lbrs def)
  = litLExprBranches <$> sequence [(,) l <$> convertExpr e | (l, e) <- lbrs]
                     <*> convertExpr def

convertBody :: Body Expr (MetaVar VarInfo s) -> TCM s (LBody (MetaVar VarInfo s))
convertBody (Constant e) = mapLifted Constant <$> convertExpr e
convertBody (Function xs s) = do
  trp "convertBody fun" $ show <$> Simple.fromScope s
  modifyIndent succ
  vars <- mapM (`forall_` Unknown) xs
  let e = instantiateVar ((vars Vector.!) . unTele) s
      abstr = unvar (const Nothing) (fmap Tele . (`Vector.elemIndex` vars))
  e' <- convertExpr e
  let result = mapLifted (Function xs . Simple.abstract abstr) e'
  modifyIndent pred
  trs "convertBody res" vars
  trp "convertBody res" $ show <$> e'
  return result
