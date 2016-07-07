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

funParamDirections :: Name -> Gen (Maybe (Direction, Vector Direction))
funParamDirections n = do
  mbody <- asks (($ n) . definitions)
  case mbody of
    Just (FunctionBody (Function d xs _)) -> return $ Just (d, snd <$> xs)
    _ -> return Nothing

type Gen = ReaderT GenEnv (State LLVMState)

runGen :: GenEnv -> Gen a -> (a, [B])
runGen f m = runLLVM $ runReaderT m f

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks $ ($ qc) . constrArity

generateGlobal :: Name -> Gen Var
generateGlobal g = do
  mbody <- asks (($ g) . definitions)
  case mbody of
    Just (ConstantBody _) -> return $ IndirectVar $ global g
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
  result <- nameHint "indirection" =: alloca (LLVM.Operand "1")
  emit $ store o result
  return result
indirect (IndirectVar o) = return o

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
  Global g -> varcpy ret (IndirectVar $ global g) sz
  Lit l -> emit $ store (shower l) ret

generateStmt :: StmtG -> Gen Var
generateStmt expr = case expr of
  Let _h e s -> do
    o <- generateStmt e
    generateStmt $ instantiate1Var o s
  Sized (Lit n) e -> generateExpr e $ shower n
  Sized sz e -> do
    szVar <- generateOperand sz
    szInt <- loadVar (nameHint "size") szVar
    ret <- nameHint "return" =: alloca szInt
    storeExpr e szInt ret
    return $ IndirectVar ret
  Case o brs -> do
    rets <- generateBranches o brs $ generateStmt >=> indirect
    res <- nameHint "caseResult" =: phiPtr rets
    return $ IndirectVar res

storeStmt :: StmtG -> LLVM.Operand Ptr -> Gen ()
storeStmt expr ret = case expr of
  Case o brs -> void $ generateBranches o brs $ \br -> storeStmt br ret
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

generateCall
  :: Direction
  -> OperandG
  -> Vector (OperandG, Direction)
  -> LLVM.Operand Int
  -> Gen Var
generateCall retDir funOperand os sz = do
  funVar <- generateOperand funOperand
  funInt <- loadVar mempty funVar
  fun <- nameHint "fun" =: bitcastToFun funInt retDir (snd <$> os)
  args <- forM os $ \(o, d) -> do
    v <- generateOperand o
    case d of
      Direct -> DirectVar <$> loadVar mempty v
      Indirect -> IndirectVar <$> indirect v
  case retDir of
    Indirect -> do
      ret <- nameHint "return" =: alloca sz
      emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
      return $ IndirectVar ret
    Direct -> do
      ret <- nameHint "call-return" =: varCall integerT fun args
      return $ DirectVar ret

generatePrim
  :: Primitive OperandG
  -> LLVM.Operand Int
  -> Gen Var
generatePrim p sz = do
  ret <- nameHint "prim" =: alloca sz
  storePrim p ret
  return $ IndirectVar ret

storeCall
  :: Direction
  -> OperandG
  -> Vector (OperandG, Direction)
  -> LLVM.Operand Ptr
  -> Gen ()
storeCall retDir funOperand os ret = do
  funVar <- generateOperand funOperand
  funInt <- loadVar mempty funVar
  fun <- nameHint "fun" =: bitcastToFun funInt retDir (snd <$> os)
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
  ref <- nameHint "ref" =: varCall pointerT "gc_alloc" [DirectVar fullSize]
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
storePrim (Primitive xs) ret = do
  strs <- forM xs $ \x -> case x of
    TextPart t -> return t
    VarPart o -> do
      v <- generateOperand o
      unOperand <$> loadVar mempty v
  res <- nameHint "prim" =: Instr (Foldable.fold strs)
  emit $ store res ret

generateBranches
  :: OperandG
  -> SimpleBranches QConstr Stmt Var
  -> (Stmt Var -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches op branches brCont = do
  expr <- (indirect <=< generateOperand) op
  postLabel <- LLVM.Operand <$> freshenName "after-branch"
  case branches of
    SimpleConBranches [(Builtin.Ref, tele, brScope)] -> mdo
      branchLabel <- LLVM.Operand <$> freshenName RefName

      emit $ branch branchLabel
      emitLabel branchLabel
      let inst = instantiateSimpleTeleVars args
      argSizes <- forMTele tele $ \_ _ sz -> do
        szVar <- generateStmt $ inst sz
        loadVar (nameHint "size") szVar
      (is, _) <- adds argSizes
      args <- Traversable.forM (Vector.zip (Vector.fromList is) $ teleNames tele) $ \(i, h) -> do
        outerPtr <- h =: getElementPtr expr i
        innerInt <- mempty =: load outerPtr
        innerPtr <- mempty =: intToPtr innerInt
        return $ IndirectVar innerPtr
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    SimpleConBranches [(QConstr _ c, tele, brScope)] -> mdo
      branchLabel <- LLVM.Operand <$> freshenName c

      emit $ branch branchLabel
      emitLabel branchLabel
      let inst = instantiateSimpleTeleVars args
      argSizes <- forMTele tele $ \_ _ sz -> do
        szVar <- generateStmt $ inst sz
        loadVar (nameHint "size") szVar
      (is, _) <- adds argSizes
      args <- Traversable.forM (Vector.zip (Vector.fromList is) $ teleNames tele) $ \(i, h) -> do
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
        argSizes <- forMTele tele $ \_ _ sz -> do
          szVar <- generateStmt $ inst sz
          loadVar (nameHint "size") szVar
        (is, _) <- adds $ Vector.cons (LLVM.Operand "1") argSizes
        args <- Traversable.forM (Vector.zip (Vector.fromList is) $ teleNames tele) $ \(i, h) -> do
          ptr <- h =: getElementPtr expr i
          return $ IndirectVar ptr
        contResult <- brCont $ inst brScope
        emit $ branch postLabel
        return contResult
      emitLabel failLabel
      emit $ exit 1
      emit unreachable
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
generateConstant name (Constant s) = do
  let gname = unOperand $ global name
      initName = gname <> "-init"
  emitRaw $ Instr $ gname <+> "= external global" <+> integerT
  emitRaw $ Instr ""
  emitRaw $ Instr $ "define private" <+> voidT <+> initName <> "() {"
  storeStmt s $ global name
  emitRaw "}"
  return $ "call" <+> voidT <+> initName <> "()"

generateBody :: Name -> BodyG -> Gen B
generateBody name body = case body of
  ConstantBody b -> generateConstant name b
  FunctionBody f -> do
    generateFunction name f
    return mempty
