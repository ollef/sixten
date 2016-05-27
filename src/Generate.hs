{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module Generate where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Foldable as Foldable
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import LLVM hiding (Operand)
import qualified LLVM
import Syntax.Branches
import Syntax.Hint
import Syntax.Lifted
import Syntax.Name
import Syntax.Telescope
import Util

data Var
  = IndirectVar (LLVM.Operand Ptr)
  | DirectVar (LLVM.Operand Int)

type OperandG = Operand Var
type ExprG = Expr Var
type StmtG = Stmt Var
type BodyG = Body Var
type BranchesG e = Branches QConstr e Var

data GenEnv = GenEnv
  { constrArity :: QConstr -> Maybe Int
  , definitions :: Name -> Maybe (Body Void)
  }

funParamDirections :: Name -> Gen (Maybe (Vector Direction))
funParamDirections n = do
  mbody <- asks (($ n) . definitions)
  case mbody of
    Just (FunctionBody (Function xs _)) -> return $ Just $ snd <$> xs
    _ -> return Nothing

type Gen = ReaderT GenEnv (State LLVMState)

runGen :: GenEnv -> Gen a -> (a, [B])
runGen f m = runLLVM $ runReaderT m f

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks $ ($ qc) . constrArity

generateOperand :: OperandG -> Gen Var
generateOperand op = case op of
  Local l -> return l
  Global g -> return (DirectVar $ LLVM.Operand $ "@" <> g) -- TODO constants?
  Lit l -> return $ DirectVar $ shower l

loadVar :: NameHint -> Var -> Gen (LLVM.Operand Int)
loadVar _ (DirectVar o) = return o
loadVar h (IndirectVar o) = h =: load o

loadVarPtr :: Var -> Gen (LLVM.Operand Ptr)
loadVarPtr (DirectVar o) = mempty =: intToPtr o
loadVarPtr (IndirectVar o) = do
  res <- mempty =: load o
  mempty =: intToPtr res

indirect :: Var -> Gen (LLVM.Operand Ptr)
indirect (DirectVar o) = do
  result <- nameHint "indirection" =: alloca ptrSize
  emit $ store o result
  return result
indirect (IndirectVar o) = return o

allocaVarWords :: NameHint -> Var -> Gen Var
allocaVarWords hint v = do
  i <- loadVar mempty v
  ptr <- allocaWords hint i
  return $ IndirectVar ptr

varcpy :: LLVM.Operand Ptr -> Var -> LLVM.Operand Int -> Gen ()
varcpy dst (DirectVar src) _sz = emit $ store src dst
varcpy dst (IndirectVar src) sz = wordcpy dst src sz

storeOperand
  :: OperandG
  -> LLVM.Operand Int
  -> LLVM.Operand Ptr
  -> Gen ()
storeOperand op sz ret = case op of
  Local l -> varcpy ret l sz
  Global g -> error "storeOperand TODO"
  Lit l -> emit $ store (shower l) ret

generateStmt :: StmtG -> Gen Var
generateStmt expr = case expr of
  Let _h e s -> do
    o <- generateStmt e
    generateStmt $ instantiate1Var o s
  Sized sz e -> do
    szVar <- generateOperand sz
    szInt <- loadVar (nameHint "size") szVar
    ret <- allocaWords (nameHint "return") szInt
    storeExpr e szInt ret
    return $ IndirectVar ret
  Case (o, _) brs -> do
    rets <- generateBranches o brs $ generateStmt >=> indirect
    res <- nameHint "caseResult" =: phiPtr rets
    return $ IndirectVar res

storeStmt :: StmtG -> LLVM.Operand Ptr -> Gen ()
storeStmt expr ret = case expr of
  Case (o, _) brs -> void $ generateBranches o brs $ \br -> storeStmt br ret
  Let _h e s -> do
    o <- generateStmt e
    storeStmt (instantiate1Var o s) ret
  Sized szOp inner -> do
    szPtr <- generateOperand szOp
    szInt <- loadVar (nameHint "size") szPtr
    storeExpr inner szInt ret

generateExpr
  :: ExprG
  -> LLVM.Operand Int
  -> Gen Var
generateExpr expr sz = case expr of
  Operand o -> generateOperand o
  Con qc os -> do
    ret <- allocaWords (nameHint "cons-cell") sz
    storeCon qc os ret
    return $ IndirectVar ret
  Call o os -> do
    ret <- allocaWords (nameHint "return") sz
    storeCall o os ret
    return $ IndirectVar ret

storeExpr
  :: ExprG
  -> LLVM.Operand Int
  -> LLVM.Operand Ptr
  -> Gen ()
storeExpr expr sz ret = case expr of
  Operand o -> storeOperand o sz ret
  Con qc os -> storeCon qc os ret
  Call o os -> storeCall o os ret

callFunVars
  :: (Foldable f, Functor f)
  => LLVM.Operand Fun
  -> f Var
  -> Instr ()
callFunVars name xs = Instr
  $ "call" <+> "void" <+> unOperand name <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ go <$> xs) <> ")"
  where
    go (DirectVar x) = integer x
    go (IndirectVar x) = pointer x

storeCall
  :: OperandG
  -> Vector OperandG
  -> LLVM.Operand Ptr
  -> Gen ()
storeCall (Global g) os ret = do
  ds <- fromMaybe (Vector.replicate (Vector.length os) Direct) <$> funParamDirections g
  args <- forM (Vector.zip os ds) $ \(o, d) -> do
    v <- generateOperand o
    case d of
      Direct -> DirectVar <$> loadVar mempty v
      Indirect -> IndirectVar <$> indirect v
  emit $ callFunVars (LLVM.Operand g) $ Vector.snoc args $ IndirectVar ret
storeCall _ _ _ = error "storeCall unknown function"

storeCon
  :: QConstr
  -> Vector (OperandG, OperandG)
  -> LLVM.Operand Ptr
  -> Gen ()
storeCon qc os ret = do
  mqcIndex <- constrIndex qc
  let os' = maybe id (\i -> Vector.cons (Lit $ fromIntegral i, Lit 1)) mqcIndex os
  sizes <- mapM (generateOperand . snd) os'
  sizeInts <- Traversable.forM sizes $ \ptr -> loadVar mempty ptr
  is <- adds sizeInts
  Foldable.forM_ (zip (Vector.toList sizeInts) $ zip is $ Vector.toList os') $ \(sz, (i, (o, _))) -> do
    index <- nameHint "index" =: getElementPtr ret i
    storeOperand o sz index

generateBranches
  :: OperandG
  -> SimpleBranches QConstr Stmt Var
  -> (Stmt Var -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches op branches brCont = do
  expr <- (indirect <=< generateOperand) op
  postLabel <- LLVM.Operand <$> freshenName "after-branch"
  case branches of
    SimpleConBranches [(QConstr _ c, tele, brScope)] -> mdo
      branchLabel <- LLVM.Operand <$> freshenName c

      emit $ branch branchLabel
      emitLabel branchLabel
      let inst = instantiateSimpleTeleVars args
      argSizes <- forMSimpleTele tele $ \_ sz -> do
        szVar <- generateStmt $ inst sz
        loadVar (nameHint "size") szVar
      is <- adds argSizes
      args <- Traversable.forM (Vector.zip (Vector.fromList is) $ simpleTeleNames tele) $ \(i, h) -> do
        ptr <- h =: getElementPtr expr i
        return $ IndirectVar ptr
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]
    SimpleConBranches cbrs -> do
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
          szVar <- generateStmt $ inst sz
          loadVar (nameHint "size") szVar
        is <- adds $ Vector.cons (LLVM.Operand "1") argSizes
        args <- Traversable.forM (Vector.zip (Vector.fromList is) $ simpleTeleNames tele) $ \(i, h) -> do
          ptr <- h =: getElementPtr expr i
          return $ IndirectVar ptr
        contResult <- brCont $ inst brScope
        emit $ branch postLabel
        return contResult
      emitLabel failLabel
      emit $ exit 1
      emit retVoid
      emitLabel postLabel
      return $ zip contResults $ snd <$> branchLabels
    SimpleLitBranches lbrs def -> do
      e0Ptr <- nameHint "tag-pointer" =: getElementPtr expr (LLVM.Operand "0")
      e0 <- nameHint "tag" =: load e0Ptr

      branchLabels <- Traversable.forM lbrs $ \(l, _) -> do
        branchLabel <- LLVM.Operand <$> freshenName (shower l)
        return (fromIntegral l, branchLabel)

      defaultLabel <- LLVM.Operand <$> freshenName "default"
      emit $ switch e0 defaultLabel branchLabels

      contResults <- Traversable.forM (zip lbrs branchLabels) $ \((_, br), (_, brLabel)) -> do
        emitLabel brLabel
        contResult <- brCont br
        emit $ branch postLabel
        return contResult

      emitLabel defaultLabel
      defaultContResult <- brCont def
      emit $ branch postLabel
      emitLabel postLabel
      return $ (defaultContResult, defaultLabel) : zip contResults (snd <$> branchLabels)


generateBody :: BodyG -> Gen ()
generateBody body = case body of
  ConstantBody _ -> return () -- TODO
  FunctionBody (Function hs e) -> do
    vs <- Traversable.forM hs $ \(h, d) -> do
      n <- freshWithHint h
      return $ case d of
        Direct -> DirectVar $ LLVM.Operand n
        Indirect -> IndirectVar $ LLVM.Operand n
    ret <- LLVM.Operand <$> freshenName "return"
    emit $ Instr $ "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList vs) <> "," <+> pointer ret <> ")"
    storeStmt (instantiateVar ((vs Vector.!) . unTele) e) ret
    emit retVoid
    where
      go (DirectVar n) = integer n
      go (IndirectVar n) = pointer n
