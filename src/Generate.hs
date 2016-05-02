{-# LANGUAGE DeriveFunctor, OverloadedStrings, RecursiveDo #-}
module Generate where

import Bound
import qualified Data.Foldable as Foldable
import Data.List
import Data.Monoid
import qualified Data.Traversable as Traversable
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
type ExprG = Expr (LLVM.Operand Ptr)
type BodyG e = Body e (LLVM.Operand Ptr)
type BranchesG e = Branches QConstr e (LLVM.Operand Ptr)

sizeOfOperand :: OperandG -> LLVM.Operand Ptr
sizeOfOperand = undefined

sizeOfExpr :: ExprG -> LLVM.Operand Ptr
sizeOfExpr expr = case expr of
  Operand o -> undefined

generateOperand :: OperandG -> Gen (LLVM.Operand Ptr)
generateOperand op = case op of
  Local l -> return $ l
  Global g -> return $ LLVM.Operand $ "@" <> g -- TODO constants?
  Lit l -> do
    litPtr <- nameHint "stacklit" =: alloca ptrSize
    emit $ store (shower l) litPtr
    return litPtr

generateExpr :: ExprG -> Gen (LLVM.Operand Ptr)
generateExpr expr = case expr of
  Operand o -> generateOperand o
  Con qc os -> do
    qcIndex <- return 123 -- TODO constrIndex qc
    let os' = Vector.cons (Lit $ fromIntegral qcIndex, Lit 1) os
    ptrs <- mapM (generateOperand . snd) os'
    ints <- Traversable.forM ptrs $ \ptr -> mempty =: load ptr
    (is, fullSize) <- adds ints
    result <- mempty =: alloca fullSize
    Foldable.forM_ (zip (Vector.toList ptrs) $ zip is $ Vector.toList os') $ \(ptr, (i, (_, sz))) -> do
      index <- nameHint "index" =: getElementPtr result i
      szPtr <- generateOperand sz
      szInt <- nameHint "size" =: load szPtr
      emit $ memcpy index ptr szInt
    return result
  Let _h e s -> do
    o <- generateExpr e
    generateExpr $ instantiate1 (pure o) s
  Call sz o os -> do
    szPtr <- generateOperand sz
    szInt <- nameHint "size" =: load szPtr
    ret <- nameHint "return" =: alloca szInt
    fptr <- generateOperand o
    f <- nameHint "f" =: bitcastToFun fptr (Vector.length os + 1)
    args <- mapM generateOperand os
    emit $ callFun f (Vector.snoc args ret)
    return ret
  Case _sz o brs -> do
    e <- generateOperand o
    generateBranches e brs

generateBranches :: LLVM.Operand Ptr -> BranchesG Expr -> Gen (LLVM.Operand Ptr)
generateBranches expr branches = case branches of
  ConBranches cbrs _ -> do
    postLabel <- LLVM.Operand <$> freshenName "afterBranches"
    e0Ptr <- nameHint "tagPtr" =: getElementPtr expr (LLVM.Operand "0")
    e0 <- nameHint "tag" =: load e0Ptr
    branchLabels <- Traversable.forM cbrs $ \(qc@(QConstr _ c), tele, brScope) -> do
      qcIndex <- return 123 -- TODO constrIndex qc
      branchLabel <- LLVM.Operand <$> freshenName c
      return (qcIndex, branchLabel)

    failLabel <- LLVM.Operand <$> freshenName "patternMatchFailure"

    emit $ switch e0 failLabel branchLabels

    branchResults <- Traversable.forM (zip cbrs branchLabels) $ \((_, tele, brScope), (_, branchLabel)) -> mdo
      emitLabel branchLabel
      let inst = instantiateTele $ pure <$> args
      argSizes <- forMTele tele $ \_ _ sz -> do
        szPtr <- generateExpr $ inst sz
        nameHint "size" =: load szPtr
      (is, _) <- adds $ Vector.cons (LLVM.Operand "1") argSizes
      args <- Traversable.forM (Vector.zip (Vector.fromList is) $ teleNames tele) $ \(i, h) ->
        h =: getElementPtr expr i
      branchResult <- generateExpr $ inst brScope
      emit $ br postLabel
      return branchResult
    emitLabel failLabel
    emit $ exit 1
    emit $ retVoid
    emitLabel postLabel
    nameHint "result" =: phiPtr [(res, l) | ((_, l), res) <- zip branchLabels branchResults]
  LitBranches _ _ -> undefined

generateBody :: BodyG Expr -> Gen ()
generateBody body = case body of
  Constant _ -> error "generateBody Constant"
  Function hs e -> do
    vs <- Traversable.forM hs $ fmap LLVM.Operand . freshWithHint
    retPtr <- LLVM.Operand <$> freshenName "return"
    emit $ Instr $ "(" <> Foldable.fold (intersperse ", " $ ptr <$> Vector.toList vs) <> "," <+> ptr retPtr <> ")"
    b <- generateExpr $ instantiate (pure . (vs Vector.!) . unTele) e
    emit $ memcpy retPtr b $ LLVM.Operand "TODO"
    emit $ retVoid
