{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving, OverloadedStrings, RecursiveDo #-}
module Generate where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Foldable as Foldable
import Data.List
import Data.Monoid
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import LLVM hiding (Operand)
import qualified LLVM
import Syntax.Branches
import Syntax.Hint
import Syntax.Lifted
import Syntax.Name
import Syntax.Telescope
import Util

type OperandG = Operand (LLVM.Operand Ptr)
type InnerExprG = InnerExpr (LLVM.Operand Ptr)
type ExprG = Expr (LLVM.Operand Ptr)
type BodyG e = Body e (LLVM.Operand Ptr)
type BranchesG e = Branches QConstr e (LLVM.Operand Ptr)

type Gen = ReaderT (QConstr -> Maybe Int) (State LLVMState)

runGen :: (QConstr -> Maybe Int) -> Gen a -> (a, [B])
runGen f m = runLLVM $ runReaderT m f

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks ($ qc)

generateOperand :: OperandG -> Gen (LLVM.Operand Ptr)
generateOperand op = case op of
  Local l -> return l
  Global g -> return $ LLVM.Operand $ "@" <> g -- TODO constants?
  Lit l -> do
    litPtr <- nameHint "stack-lit" =: alloca ptrSize
    emit $ store (shower l) litPtr
    return litPtr

storeOperand
  :: OperandG
  -> LLVM.Operand Int
  -> LLVM.Operand Ptr
  -> Gen ()
storeOperand op sz ret = case op of
  Local l -> emit $ memcpy ret l sz
  Global g -> error "storeOperand TODO"
  Lit l -> emit $ store (shower l) ret

generateExpr :: ExprG -> Gen (LLVM.Operand Ptr)
generateExpr expr = case expr of
  Let _h e s -> do
    o <- generateExpr e
    generateExpr $ instantiate1Var o s
  Sized sz e -> do
    szPtr <- generateOperand sz
    szInt <- nameHint "size" =: load szPtr
    ret <- nameHint "return" =: alloca szInt
    storeInnerExpr e szInt ret
    return ret
  Case (o, _) brs -> do
    rets <- generateBranches o brs generateExpr
    nameHint "caseResult" =: phiPtr rets

generateInnerExpr
  :: InnerExprG
  -> LLVM.Operand Int
  -> Gen (LLVM.Operand Ptr)
generateInnerExpr expr sz = case expr of
  Operand o -> generateOperand o
  Con qc os -> do
    ret <- nameHint "cons-cell" =: alloca sz
    storeCon qc os ret
    return ret
  Call o os -> do
    ret <- nameHint "return" =: alloca sz
    storeCall o os ret
    return ret

storeExpr :: ExprG -> LLVM.Operand Ptr -> Gen ()
storeExpr expr ret = case expr of
  Case (o, _) brs -> void $ generateBranches o brs $ \br -> storeExpr br ret
  Let _h e s -> do
    o <- generateExpr e
    storeExpr (instantiate1Var o s) ret
  Sized szOp inner -> do
    szPtr <- generateOperand szOp
    szInt <- nameHint "size" =: load szPtr
    storeInnerExpr inner szInt ret

storeInnerExpr
  :: InnerExprG
  -> LLVM.Operand Int
  -> LLVM.Operand Ptr
  -> Gen ()
storeInnerExpr expr sz ret = case expr of
  Operand o -> storeOperand o sz ret
  Con qc os -> storeCon qc os ret
  Call o os -> storeCall o os ret

storeCall
  :: OperandG
  -> Vector OperandG
  -> LLVM.Operand Ptr
  -> Gen ()
storeCall o os ret = do
  fptr <- generateOperand o
  f <- nameHint "function" =: bitcastToFun fptr (Vector.length os + 1)
  args <- mapM generateOperand os
  emit $ callFun f (Vector.snoc args ret)

storeCon
  :: QConstr
  -> Vector (OperandG, OperandG)
  -> LLVM.Operand Ptr
  -> Gen ()
storeCon qc os ret = do
  mqcIndex <- constrIndex qc
  let os' = maybe id (\i -> Vector.cons (Lit $ fromIntegral i, Lit 1)) mqcIndex os
  ptrs <- mapM (generateOperand . snd) os'
  ints <- Traversable.forM ptrs $ \ptr -> mempty =: load ptr
  is <- adds ints
  Foldable.forM_ (zip (Vector.toList ptrs) $ zip is $ Vector.toList os') $ \(ptr, (i, (_, sz))) -> do
    index <- nameHint "index" =: getElementPtr ret i
    szPtr <- generateOperand sz
    szInt <- nameHint "size" =: load szPtr
    emit $ memcpy index ptr szInt

generateBranches
  :: OperandG
  -> SimpleBranches QConstr Expr (LLVM.Operand Ptr)
  -> (Expr (LLVM.Operand Ptr) -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches op branches brCont = do
  expr <- generateOperand op
  case branches of
    SimpleConBranches [(QConstr _ c, tele, brScope)] -> mdo
      postLabel <- LLVM.Operand <$> freshenName "after-branch"
      branchLabel <- LLVM.Operand <$> freshenName c

      emit $ branch branchLabel
      emitLabel branchLabel
      let inst = instantiateSimpleTeleVars args
      argSizes <- forMSimpleTele tele $ \_ sz -> do
        szPtr <- generateExpr $ inst sz
        nameHint "size" =: load szPtr
      is <- adds argSizes
      args <- Traversable.forM (Vector.zip (Vector.fromList is) $ simpleTeleNames tele) $ \(i, h) ->
        h =: getElementPtr expr i
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]
    SimpleConBranches cbrs -> do
      postLabel <- LLVM.Operand <$> freshenName "after-branches"
      e0Ptr <- nameHint "tag-pointer" =: getElementPtr expr (LLVM.Operand "0")
      e0 <- nameHint "tag" =: load e0Ptr
      branchLabels <- Traversable.forM cbrs $ \(qc@(QConstr _ c), _, _) -> do
        Just qcIndex <- constrIndex qc
        branchLabel <- LLVM.Operand <$> freshenName c
        return (qcIndex, branchLabel)

      failLabel <- LLVM.Operand <$> freshenName "pattern-match-failed"

      emit $ switch e0 failLabel branchLabels

      contResults <- Traversable.forM (zip cbrs branchLabels) $ \((_, tele, brScope), (_, branchLabel)) -> mdo
        emitLabel branchLabel
        let inst = instantiateSimpleTeleVars args
        argSizes <- forMSimpleTele tele $ \_ sz -> do
          szPtr <- generateExpr $ inst sz
          nameHint "size" =: load szPtr
        is <- adds $ Vector.cons (LLVM.Operand "1") argSizes
        args <- Traversable.forM (Vector.zip (Vector.fromList is) $ simpleTeleNames tele) $ \(i, h) ->
          h =: getElementPtr expr i
        contResult <- brCont $ inst brScope
        emit $ branch postLabel
        return contResult
      emitLabel failLabel
      emit $ exit 1
      emit retVoid
      emitLabel postLabel
      return $ zip contResults $ snd <$> branchLabels
    SimpleLitBranches _ _ -> undefined -- TODO

generateBody :: BodyG Expr -> Gen ()
generateBody body = case body of
  Constant _ -> return () -- TODO
  Function hs e -> do
    vs <- Traversable.forM hs $ fmap LLVM.Operand . freshWithHint
    ret <- LLVM.Operand <$> freshenName "return"
    emit $ Instr $ "(" <> Foldable.fold (intersperse ", " $ pointer <$> Vector.toList vs) <> "," <+> pointer ret <> ")"
    storeExpr (instantiateVar ((vs Vector.!) . unTele) e) ret
    emit $ retVoid
