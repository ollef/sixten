{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module Generate where

import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Foldable as Foldable
import Data.List
import Data.Monoid
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Builtin
import LLVM hiding (Operand)
import qualified LLVM
import Syntax.Branches
import Syntax.Direction
import Syntax.Hint
import Syntax.Name
import Syntax.Primitive
import Syntax.Restricted
import Syntax.Telescope
import Util

data Var
  = IndirectVar (LLVM.Operand Ptr)
  | DirectVar (LLVM.Operand Int)
  deriving Show

varDir :: Var -> Direction
varDir (IndirectVar _) = Indirect
varDir (DirectVar _) = Direct

type OperandG = Operand Var
type ExprG = Expr Var
type StmtG = Stmt Var
type BodyG = Body Var
type ConstantG = Constant Var
type FunctionG = Function Var
type BranchesG e = Branches QConstr e Var

data GenEnv = GenEnv
  { constrArity :: QConstr -> Maybe Int
  , definitions :: Name -> Maybe (Body Void)
  }

type Gen = ReaderT GenEnv (State LLVMState)

runGen :: GenEnv -> Gen a -> (a, [B])
runGen f m = runLLVM $ runReaderT m f

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks $ ($ qc) . constrArity

generateGlobal :: Name -> Gen Var
generateGlobal g = do
  mbody <- asks (($ g) . definitions)
  case mbody of
    Just (ConstantBody (Constant Direct _)) -> do
      return $ IndirectVar $ global g
    Just (ConstantBody (Constant Indirect _)) -> do
      ptr <- nameHint "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (FunctionBody (Function retDir args _)) -> return
      $ DirectVar
      $ ptrToIntExpr
      $ bitcastFunToPtrExpr (global g) retDir $ snd <$> args
    _ -> return $ DirectVar $ global g

generateOperand :: OperandG -> Gen Var
generateOperand op = case op of
  Local l -> return l
  Global g -> generateGlobal g
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
  result <- nameHint "indirection" =: alloca "1"
  emit $ store o result
  return result
indirect (IndirectVar o) = return o

varToPtr :: Var -> Gen (LLVM.Operand Ptr)
varToPtr (DirectVar o) = nameHint "ptr" =: intToPtr o
varToPtr (IndirectVar o) = return o

allocaVar :: NameHint -> Var -> Gen Var
allocaVar hint v = do
  i <- loadVar mempty v
  ptr <- hint =: alloca i
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
  Global g -> do
    v <- generateGlobal g
    varcpy ret v sz
  Lit l -> emit $ store (shower l) ret

generateStmt :: StmtG -> Gen Var
generateStmt stmt = case stmt of
  Sized sz e -> do
    szVar <- generateOperand sz
    szInt <- loadVar (nameHint "size") szVar
    generateExpr e szInt
  Let _h e s -> do
    o <- generateStmt e
    generateStmt $ instantiate1Var o s
  Case o brs -> do
    rets <- generateBranches o brs $ generateStmt >=> indirect
    res <- nameHint "caseResult" =: phiPtr rets
    return $ IndirectVar res

storeStmt :: StmtG -> LLVM.Operand Ptr -> Gen ()
storeStmt stmt ret = case stmt of
  Case o brs -> void $ generateBranches o brs $ \br -> storeStmt br ret
  Let _h e s -> do
    o <- generateStmt e
    storeStmt (instantiate1Var o s) ret
  Sized szOp inner -> do
    szVar <- generateOperand szOp
    szInt <- loadVar (nameHint "size") szVar
    storeExpr inner szInt ret

gcAllocStmt :: StmtG -> Gen (LLVM.Operand Ptr)
gcAllocStmt stmt = case stmt of
  Sized sz e -> do
    szVar <- generateOperand sz
    szInt <- loadVar (nameHint "size") szVar
    res <- gcAlloc szInt
    storeExpr e szInt res
    return res
  Let _h e s -> do
    o <- generateStmt e
    gcAllocStmt $ instantiate1Var o s
  Case o brs -> do
    results <- generateBranches o brs gcAllocStmt
    nameHint "case-result" =: phiPtr results

generateExpr
  :: ExprG
  -> LLVM.Operand Int
  -> Gen Var
generateExpr expr sz = case expr of
  Operand o -> generateOperand o
  Con qc os -> do
    ret <- nameHint "cons-cell" =: alloca sz
    storeCon qc os ret
    return $ IndirectVar ret
  Call retDir o os -> generateCall retDir o os sz
  Prim p -> generatePrim p sz

storeExpr
  :: ExprG
  -> LLVM.Operand Int
  -> LLVM.Operand Ptr
  -> Gen ()
storeExpr expr sz ret = case expr of
  Operand o -> storeOperand o sz ret
  Con qc os -> storeCon qc os ret
  Call retDir o os -> storeCall retDir o os ret
  Prim p -> storePrim p ret

varCall
  :: (Foldable f, Functor f)
  => B
  -> LLVM.Operand Fun
  -> f Var
  -> Instr a
varCall retType name xs = Instr
  $ "call" <+> retType <+> unOperand name <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ go <$> xs) <> ")"
  where
    go (DirectVar x) = integer x
    go (IndirectVar x) = pointer x

generateFunOperand
  :: OperandG
  -> Direction
  -> Vector Direction
  -> Gen (LLVM.Operand Fun)
generateFunOperand (Global g) _ _ = return $ global g
generateFunOperand op retDir argDirs = do
  funVar <- generateOperand op
  funPtr <- loadVarPtr funVar
  nameHint "fun" =: bitcastToFun funPtr retDir argDirs

generateCall
  :: Direction
  -> OperandG
  -> Vector (OperandG, Direction)
  -> LLVM.Operand Int
  -> Gen Var
generateCall retDir funOperand os sz = do
  fun <- generateFunOperand funOperand retDir $ snd <$> os
  args <- forM os $ \(o, d) -> do
    v <- generateOperand o
    case d of
      Direct -> DirectVar <$> loadVar mempty v
      Indirect -> IndirectVar <$> indirect v
  case retDir of
    Indirect -> do
      ret <- nameHint "call-return" =: alloca sz
      emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
      return $ IndirectVar ret
    Direct -> do
      ret <- nameHint "call-return" =: varCall integerT fun args
      return $ DirectVar ret

generatePrim
  :: Primitive OperandG
  -> LLVM.Operand Int
  -> Gen Var
generatePrim (Primitive xs) _ = do
  strs <- forM xs $ \x -> case x of
    TextPart t -> return t
    VarPart o -> do
      v <- generateOperand o
      unOperand <$> loadVar mempty v
  ret <- nameHint "prim" =: Instr (Foldable.fold strs)
  return $ DirectVar ret

storeCall
  :: Direction
  -> OperandG
  -> Vector (OperandG, Direction)
  -> LLVM.Operand Ptr
  -> Gen ()
storeCall retDir funOperand os ret = do
  fun <- generateFunOperand funOperand retDir $ snd <$> os
  args <- forM os $ \(o, d) -> do
    v <- generateOperand o
    case d of
      Direct -> DirectVar <$> loadVar mempty v
      Indirect -> IndirectVar <$> indirect v
  case retDir of
    Indirect -> emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
    Direct -> do
      res <- nameHint "call-return" =: varCall integerT fun args
      emit $ store res ret

storeCon
  :: QConstr
  -> Vector (OperandG, OperandG)
  -> LLVM.Operand Ptr
  -> Gen ()
storeCon Builtin.Ref os ret = do
  sizes <- mapM (generateOperand . snd) os
  sizeInts <- Traversable.forM sizes $ \ptr -> loadVar mempty ptr
  (is, fullSize) <- adds sizeInts
  ref <- gcAlloc fullSize
  Foldable.forM_ (zip (Vector.toList sizeInts) $ zip is $ Vector.toList os) $ \(sz, (i, (o, _))) -> do
    index <- nameHint "index" =: getElementPtr ref i
    storeOperand o sz index
  refInt <- nameHint "ref-int" =: ptrToInt ref
  emit $ store refInt ret
storeCon qc os ret = do
  mqcIndex <- constrIndex qc
  let os' = maybe id (\i -> Vector.cons (Lit $ fromIntegral i, Lit 1)) mqcIndex os
  sizes <- mapM (generateOperand . snd) os'
  sizeInts <- Traversable.forM sizes $ \ptr -> loadVar mempty ptr
  (is, _) <- adds sizeInts
  Foldable.forM_ (zip (Vector.toList sizeInts) $ zip is $ Vector.toList os') $ \(sz, (i, (o, _))) -> do
    index <- nameHint "index" =: getElementPtr ret i
    storeOperand o sz index

storePrim
  :: Primitive OperandG
  -> LLVM.Operand Ptr
  -> Gen ()
storePrim p ret = do
  res <- generatePrim p $ LLVM.Operand "1"
  intRes <- loadVar (nameHint "loaded-prim") res
  emit $ store intRes ret

generateBranches
  :: OperandG
  -> SimpleBranches QConstr Stmt Var
  -> (Stmt Var -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches op branches brCont = do
  expr <- (varToPtr <=< generateOperand) op
  postLabel <- LLVM.Operand <$> freshenName "after-branch"
  case branches of
    SimpleConBranches [(Builtin.Ref, tele, brScope)] -> mdo
      branchLabel <- LLVM.Operand <$> freshenName Builtin.RefName

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateSimpleTeleVars $ Vector.fromList $ reverse revArgs
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateStmt $ inst s
                szInt <- loadVar (nameHint "size") sz
                nameHint "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    SimpleConBranches [(QConstr _ c, tele, brScope)] -> mdo
      branchLabel <- LLVM.Operand <$> freshenName c

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateSimpleTeleVars $ Vector.fromList $ reverse revArgs
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateStmt $ inst s
                szInt <- loadVar (nameHint "size") sz
                nameHint "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    SimpleConBranches cbrs -> do
      e0Ptr <- nameHint "tag-pointer" =: getElementPtr expr "0"
      e0 <- nameHint "tag" =: load e0Ptr

      branchLabels <- Traversable.forM cbrs $ \(qc@(QConstr _ c), _, _) -> do
        Just qcIndex <- constrIndex qc
        branchLabel <- LLVM.Operand <$> freshenName c
        return (qcIndex, branchLabel)

      failLabel <- LLVM.Operand <$> freshenName "pattern-match-failed"
      emit $ switch e0 failLabel branchLabels

      contResults <- Traversable.forM (zip cbrs branchLabels) $ \((_, tele, brScope), (_, branchLabel)) -> mdo
        emitLabel branchLabel

        let teleVector = Vector.indexed $ unTelescope tele
            inst = instantiateSimpleTeleVars $ Vector.fromList $ reverse revArgs
            go (vs, index) (i, (h, (), s)) = do
              ptr <- h =: getElementPtr expr index
              nextIndex <- if i == Vector.length teleVector - 1
                then return index
                else do
                  sz <- generateStmt $ inst s
                  szInt <- loadVar (nameHint "size") sz
                  nameHint "index" =: add index szInt
              return (IndirectVar ptr : vs, nextIndex)

        (revArgs, _) <- Foldable.foldlM go (mempty, "1") teleVector
        contResult <- brCont $ inst brScope
        emit $ branch postLabel
        return contResult

      emitLabel failLabel
      emit $ exit 1
      emit unreachable
      emitLabel postLabel
      return $ zip contResults $ snd <$> branchLabels

    SimpleLitBranches lbrs def -> do
      e0Ptr <- nameHint "lit-pointer" =: getElementPtr expr "0"
      e0 <- nameHint "lit" =: load e0Ptr

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

generateFunction :: Name -> FunctionG -> Gen ()
generateFunction name (Function retDir hs e) = do
  vs <- Traversable.forM hs $ \(h, d) -> do
    n <- freshWithHint h
    return $ case d of
      Direct -> DirectVar $ LLVM.Operand n
      Indirect -> IndirectVar $ LLVM.Operand n
  case retDir of
    Indirect -> do
      ret <- LLVM.Operand <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> voidT <+> "@" <> name <> "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeStmt (instantiateVar ((vs Vector.!) . unTele) e) ret
      emit returnVoid
      emitRaw "}"
    Direct -> do
      emitRaw $ Instr $ "define" <+> integerT <+> "@" <> name <> "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList vs) <> ") {"
      res <- generateStmt $ instantiateVar ((vs Vector.!) . unTele) e
      resInt <- loadVar mempty res
      emit $ returnInt resInt
      emitRaw "}"
  where
    go (DirectVar n) = integer n
    go (IndirectVar n) = pointer n

generateConstant :: Name -> ConstantG -> Gen B
generateConstant name (Constant dir s) = do
  let gname = unOperand $ global name
      initName = gname <> "-init"
  emitRaw $ Instr $ gname <+> "= global" <+> typVal <> ", align" <+> align
  emitRaw $ Instr ""
  emitRaw $ Instr $ "define private" <+> voidT <+> initName <> "() {"
  case dir of
    Direct -> storeStmt s $ global name
    Indirect -> do
      ptr <- gcAllocStmt s
      emit $ storePtr ptr $ global name
  emit returnVoid
  emitRaw "}"
  return $ "  call" <+> voidT <+> initName <> "()"
  where
    typVal = case dir of
      Direct -> integer "0"
      Indirect -> pointer "null"

generateBody :: Name -> BodyG -> Gen B
generateBody name body = case body of
  ConstantBody b -> generateConstant name b
  FunctionBody f -> do
    generateFunction name f
    return mempty
