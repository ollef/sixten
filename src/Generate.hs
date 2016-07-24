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
import LLVM
import Syntax.Branches
import qualified Syntax.Converted as Converted
import Syntax.Direction
import Syntax.Hint
import Syntax.Name
import Syntax.Primitive
import Syntax.Lifted
import Syntax.Telescope
import Util

-------------------------------------------------------------------------------
-- Generation environment
data GenEnv = GenEnv
  { constrArity :: QConstr -> Maybe Int
  , signatures :: Name -> Maybe (Converted.Signature Converted.Expr Unit Void)
  }

type Gen = ReaderT GenEnv (State LLVMState)

runGen :: GenEnv -> Gen a -> (a, [B])
runGen f m = runLLVM $ runReaderT m f

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks $ ($ qc) . constrArity

-------------------------------------------------------------------------------
-- Vars
data Var
  = IndirectVar (Operand Ptr)
  | DirectVar (Operand Int)
  deriving Show

varDir :: Var -> Direction
varDir (IndirectVar _) = Indirect
varDir (DirectVar _) = Direct

loadVar :: NameHint -> Var -> Gen (Operand Int)
loadVar _ (DirectVar o) = return o
loadVar h (IndirectVar o) = h =: load o

indirect :: NameHint -> Var -> Gen (Operand Ptr)
indirect n (DirectVar o) = do
  result <- n =: alloca "1"
  emit $ store o result
  return result
indirect _ (IndirectVar o) = return o

varcpy :: Operand Ptr -> Var -> Operand Int -> Gen ()
varcpy dst (DirectVar src) _sz = emit $ store src dst
varcpy dst (IndirectVar src) sz = wordcpy dst src sz

varCall
  :: (Foldable f, Functor f)
  => B
  -> Operand Fun
  -> f Var
  -> Instr a
varCall retType name xs = Instr
  $ "call" <+> retType <+> unOperand name 
  <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ go <$> xs) <> ")"
  where
    go (DirectVar x) = integer x
    go (IndirectVar x) = pointer x

directed
  :: Direction
  -> Var
  -> Gen Var
directed d v = case d of
  Direct -> DirectVar <$> loadVar mempty v
  Indirect -> IndirectVar <$> indirect mempty v

-------------------------------------------------------------------------------
-- Generation
generateSExpr :: SExpr Var -> Gen Var
generateSExpr (Sized sz expr) = do
  szVar <- generateExpr "1" sz
  szInt <- loadVar (nameHint "size") szVar
  generateExpr szInt expr

storeSExpr :: SExpr Var -> Operand Ptr -> Gen ()
storeSExpr (Sized sz expr) ret = do
  szVar <- generateExpr "1" sz
  szInt <- loadVar (nameHint "size") szVar
  storeExpr szInt expr ret

generateExpr :: Operand Int -> Expr Var -> Gen Var
generateExpr sz expr = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit l -> return $ DirectVar $ shower l
  Con qc es -> do
    ret <- nameHint "cons-cell" =: alloca sz
    storeCon qc es ret
    return $ IndirectVar ret
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedSExpr) es
    case retDir of
      Indirect -> do
        ret <- nameHint "call-return" =: alloca sz
        emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
        return $ IndirectVar ret
      Direct -> do
        ret <- nameHint "call-return" =: varCall integerT fun args
        return $ DirectVar ret
  Let _h e s -> do
    v <- generateSExpr e
    generateExpr sz $ instantiate1Var v s
  Case e brs -> do

    rets <- generateBranches e brs $ \br -> do
      -- TODO Can we avoid indirection when all branches return direct vars?
      ret <- generateExpr sz br
      indirect (nameHint "indirect-br-result") ret
    fmap IndirectVar $ nameHint "case-result" =: phiPtr rets
  Prim p -> generatePrim p

storeExpr :: Operand Int -> Expr Var -> Operand Ptr -> Gen ()
storeExpr sz expr ret = case expr of
  Var v -> varcpy ret v sz
  Global g -> do
    v <- generateGlobal g
    varcpy ret v sz
  Lit l -> emit $ store (shower l) ret
  Con qc es -> storeCon qc es ret
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedSExpr) es
    case retDir of
      Indirect -> emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
      Direct -> do
        res <- nameHint "call-return" =: varCall integerT fun args
        emit $ store res ret
  Let _h e s -> do
    v <- generateSExpr e
    storeExpr sz (instantiate1Var v s) ret
  Case e brs -> void $ generateBranches e brs $ \br -> storeExpr sz br ret
  Prim p -> do
    res <- generatePrim p
    intRes <- loadVar (nameHint "loaded-prim") res
    emit $ store intRes ret

generateDirectedSExpr
  :: SExpr Var
  -> Direction
  -> Gen Var
generateDirectedSExpr expr dir
  = generateSExpr expr >>= directed dir

gcAllocSExpr :: SExpr Var -> Gen (Operand Ptr)
gcAllocSExpr (Sized sz expr) = do
  szVar <- generateExpr "1" sz
  szInt <- loadVar (nameHint "size") szVar
  ref <- gcAlloc szInt
  storeExpr szInt expr ref
  return ref

storeCon :: QConstr -> Vector (SExpr Var) -> Operand Ptr -> Gen ()
storeCon Builtin.Ref es ret = do
  sizes <- mapM (loadVar (nameHint "size") <=< generateExpr "1" . sizeOf) es
  (is, fullSize) <- adds sizes
  ref <- gcAlloc fullSize
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es) $ \(sz, (i, Sized _ e)) -> do
    index <- nameHint "index" =: getElementPtr ref i
    storeExpr sz e index
  refInt <- nameHint "ref-int" =: ptrToInt ref
  emit $ store refInt ret
storeCon qc es ret = do
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . sized 1 . Lit . fromIntegral) mqcIndex es
  sizes <- mapM (loadVar (nameHint "size") <=< generateExpr "1" . sizeOf) es'
  (is, _) <- adds sizes
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es') $ \(sz, (i, Sized _ e)) -> do
    index <- nameHint "index" =: getElementPtr ret i
    storeExpr sz e index

generateFunOp :: Expr Var -> Direction -> Vector Direction -> Gen (Operand Fun)
generateFunOp (Global g) _ _ = return $ global g
generateFunOp e retDir argDirs = do
  funVar <- generateExpr "1" e
  funInt <- loadVar (nameHint "func-int") funVar
  funPtr <- nameHint "func-ptr" =: intToPtr funInt
  nameHint "func" =: bitcastToFun funPtr retDir argDirs

generateGlobal :: Name -> Gen Var
generateGlobal g = do
  mdef <- asks (($ g) . signatures)
  case mdef of
    Just (Converted.Constant Direct _) ->
      return $ IndirectVar $ global g
    Just (Converted.Constant Indirect _) -> do
      ptr <- nameHint "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (Converted.Function retDir args _) -> return
      $ DirectVar
      $ ptrToIntExpr
      $ bitcastFunToPtrExpr (global g) retDir $ teleAnnotations args
    _ -> return $ DirectVar $ global g

generateBranches
  :: SExpr Var
  -> SimpleBranches QConstr Expr Var
  -> (Expr Var -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches caseExpr branches brCont = do
  postLabel <- LLVM.Operand <$> freshenName "after-branch"
  case branches of
    SimpleConBranches [(Builtin.Ref, tele, brScope)] -> mdo
      exprInt <- loadVar (nameHint "case-expr-int") =<< generateSExpr caseExpr
      expr <- nameHint "case-expr" =: intToPtr exprInt
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
                sz <- generateExpr "1" $ inst s
                szInt <- loadVar (nameHint "size") sz
                nameHint "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    SimpleConBranches [(QConstr _ c, tele, brScope)] -> mdo
      expr <- indirect (nameHint "case-expr") =<< generateSExpr caseExpr
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
                sz <- generateExpr "1" $ inst s
                szInt <- loadVar (nameHint "size") sz
                nameHint "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    SimpleConBranches cbrs -> do
      expr <- indirect (nameHint "case-expr") =<< generateSExpr caseExpr
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
                  sz <- generateExpr "1" $ inst s
                  szInt <- loadVar (nameHint "size") sz
                  nameHint "index" =: add index szInt
              return (IndirectVar ptr : vs, nextIndex)

        (revArgs, _) <- Foldable.foldlM go (mempty, "1") teleVector
        contResult <- brCont $ inst brScope
        emit $ branch postLabel
        return contResult

      emitLabel failLabel
      -- emit $ exit 1
      emit unreachable
      emitLabel postLabel
      return $ zip contResults $ snd <$> branchLabels

    SimpleLitBranches lbrs def -> do
      e0 <- loadVar (nameHint "lit") =<< generateSExpr caseExpr

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

generatePrim
  :: Primitive (Expr Var)
  -> Gen Var
generatePrim (Primitive xs) = do
  strs <- forM xs $ \x -> case x of
    TextPart t -> return t
    VarPart o -> do
      v <- generateExpr "1" o
      unOperand <$> loadVar mempty v
  ret <- nameHint "prim" =: Instr (Foldable.fold strs)
  return $ DirectVar ret

generateConstant :: Name -> Constant Var -> Gen B
generateConstant name (Constant dir e) = do
  let gname = unOperand $ global name
      initName = gname <> "-init"
  emitRaw $ Instr $ gname <+> "= global" <+> typVal <> ", align" <+> align
  emitRaw $ Instr ""
  emitRaw $ Instr $ "define private" <+> voidT <+> initName <> "() {"
  case dir of
    Direct -> storeSExpr e $ global name
    Indirect -> do
      ptr <- gcAllocSExpr e
      emit $ storePtr ptr $ global name
  emit returnVoid
  emitRaw "}"
  return $ "  call" <+> voidT <+> initName <> "()"
  where
    typVal = case dir of
      Direct -> integer "0"
      Indirect -> pointer "null"

generateFunction :: Name -> Function Var -> Gen ()
generateFunction name (Function retDir hs funScope) = do
  vs <- Traversable.forM hs $ \(h, d) -> do
    n <- freshWithHint h
    return $ case d of
      Direct -> DirectVar $ LLVM.Operand n
      Indirect -> IndirectVar $ LLVM.Operand n
  let funExpr = instantiateVar ((vs Vector.!) . unTele) funScope
  case retDir of
    Indirect -> do
      ret <- LLVM.Operand <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> voidT <+> "@" <> name
        <> "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeSExpr funExpr ret
      emit returnVoid
    Direct -> do
      emitRaw $ Instr $ "define" <+> integerT <+> "@" <> name <> "(" <> Foldable.fold (intersperse ", " $ go <$> Vector.toList vs) <> ") {"
      res <- generateSExpr funExpr
      resInt <- loadVar (nameHint "function-result") res
      emit $ returnInt resInt
  emitRaw "}"
  where
    go (DirectVar n) = integer n
    go (IndirectVar n) = pointer n

generateDefinition :: Name -> Definition Var -> Gen B
generateDefinition name def = case def of
  ConstantDef c -> generateConstant name c
  FunctionDef f -> do
    generateFunction name f
    return mempty
