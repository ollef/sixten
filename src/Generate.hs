{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module Generate where

import qualified Bound
import Control.Monad.State
import Control.Monad.Reader
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.Foldable as Foldable
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Builtin
import LLVM
import Syntax.Annotation
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
  = VoidVar
  | IndirectVar (Operand Ptr)
  | DirectVar (Operand Int)
  deriving Show

varDir :: Var -> Direction
varDir VoidVar = Void
varDir (IndirectVar _) = Indirect
varDir (DirectVar _) = Direct

loadVar :: NameHint -> Var -> Gen (Operand Int)
loadVar _ VoidVar = return "0"
loadVar _ (DirectVar o) = return o
loadVar h (IndirectVar o) = h =: load o

indirect :: NameHint -> Var -> Gen (Operand Ptr)
indirect _ VoidVar = return "null"
indirect n (DirectVar o) = do
  result <- n =: alloca "1"
  emit $ store o result
  return result
indirect _ (IndirectVar o) = return o

varcpy :: Operand Ptr -> Var -> Operand Int -> Gen ()
varcpy _dst VoidVar _sz = return ()
varcpy dst (DirectVar src) _sz = emit $ store src dst
varcpy dst (IndirectVar src) sz = wordcpy dst src sz

varCall
  :: (Foldable f, Functor f)
  => B
  -> Operand Fun
  -> f Var
  -> Instr a
varCall retType name xs = Instr
  $ "call fastcc" <+> retType <+> unOperand name
  <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ concat $ go <$> xs) <> ")"
  where
    go VoidVar = []
    go (DirectVar x) = [integer x]
    go (IndirectVar x) = [pointer x]

directed
  :: Direction
  -> Var
  -> Gen Var
directed d v = case d of
  Void -> return VoidVar
  Direct -> DirectVar <$> loadVar mempty v
  Indirect -> IndirectVar <$> indirect mempty v

-------------------------------------------------------------------------------
-- Generation
generateExpr :: Maybe (Operand Int) -> Expr Var -> Gen Var
generateExpr msz expr = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit l -> return $ DirectVar $ shower l
  Con qc es -> generateCon sz qc es
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedExpr) es
    case retDir of
      Void -> do
        emit $ varCall voidT fun args
        return VoidVar
      Indirect -> do
        ret <- "call-return" =: alloca sz
        emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
        return $ IndirectVar ret
      Direct -> do
        ret <- "call-return" =: varCall integerT fun args
        return $ DirectVar ret
  Let _h e s -> do
    v <- generateExpr Nothing e
    generateExpr msz $ Bound.instantiate1 (pure v) s
  Case e brs -> mdo
    rets <- generateBranches e brs $ \br -> do
      v <- generateExpr msz br
      let mdirectRet = case v of
            VoidVar -> Just "0"
            IndirectVar _ -> Nothing
            DirectVar o -> Just o
      indirectRet <- if shouldIndirect
        then indirect mempty v
        else return "null"
      return (mdirectRet, indirectRet)
    let mdirectRets = traverse (bitraverse fst pure) rets
        shouldIndirect = isNothing mdirectRets
    case mdirectRets of
      Just directRets -> fmap DirectVar $ "case-result" =: phiInt directRets
      Nothing -> fmap IndirectVar $ "case-result" =: phiPtr (first snd <$> rets)
  Prim p -> generatePrim p
  Sized size e -> do
    szVar <- generateExpr (Just "1") size
    szInt <- loadVar "size" szVar
    generateExpr (Just szInt) e
  where
    sz = fromMaybe (error "generateExpr") msz

storeExpr :: Maybe (Operand Int) -> Expr Var -> Operand Ptr -> Gen ()
storeExpr msz expr ret = case expr of
  Var v -> varcpy ret v sz
  Global g -> do
    v <- generateGlobal g
    varcpy ret v sz
  Lit l -> emit $ store (shower l) ret
  Con qc es -> storeCon qc es ret
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedExpr) es
    case retDir of
      Void -> emit $ varCall voidT fun args
      Indirect -> emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
      Direct -> do
        res <- "call-return" =: varCall integerT fun args
        emit $ store res ret
  Let _h e s -> do
    v <- generateExpr Nothing e
    storeExpr msz (Bound.instantiate1 (pure v) s) ret
  Case e brs -> void $ generateBranches e brs $ \br -> storeExpr msz br ret
  Prim p -> do
    res <- generatePrim p
    intRes <- loadVar "loaded-prim" res
    emit $ store intRes ret
  Sized size e -> do
    szVar <- generateExpr (Just "1") size
    szInt <- loadVar "size" szVar
    storeExpr (Just szInt) e ret
  where
    sz = fromMaybe (error "storeExpr") msz

generateDirectedExpr
  :: Expr Var
  -> Direction
  -> Gen Var
generateDirectedExpr expr dir
  = generateExpr Nothing expr >>= directed dir

gcAllocExpr :: Expr Var -> Gen (Operand Ptr)
gcAllocExpr (Sized sz expr) = do
  szVar <- generateExpr (Just "1") sz
  szInt <- loadVar "size" szVar
  ref <- gcAlloc szInt
  storeExpr (Just szInt) expr ref
  return ref
gcAllocExpr _ = error "gcAllocExpr"

generateCon :: Operand Int -> QConstr -> Vector (Expr Var) -> Gen Var
generateCon _ Builtin.Ref es = do
  sizes <- mapM (loadVar "size" <=< generateExpr (Just "1") . sizeOf) es
  (is, fullSize) <- adds sizes
  ref <- gcAlloc fullSize
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es) $ \(sz, (i, Sized _ e)) -> do
    index <- "index" =: getElementPtr ref i
    storeExpr (Just sz) e index
  refInt <- "ref-int" =: ptrToInt ref
  return $ DirectVar refInt
generateCon sz qc es = do
  ret <- "cons-cell" =: alloca sz
  storeCon qc es ret
  return $ IndirectVar ret

storeCon :: QConstr -> Vector (Expr Var) -> Operand Ptr -> Gen ()
storeCon Builtin.Ref es ret = do
  v <- generateCon "1" Builtin.Ref es
  i <- loadVar mempty v
  emit $ store i ret
storeCon qc es ret = do
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . sized 1 . Lit . fromIntegral) mqcIndex es
  sizes <- mapM (loadVar "size" <=< generateExpr (Just "1") . sizeOf) es'
  (is, _) <- adds sizes
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es') $ \(sz, (i, Sized _ e)) -> do
    index <- "index" =: getElementPtr ret i
    storeExpr (Just sz) e index

generateFunOp :: Expr Var -> Direction -> Vector Direction -> Gen (Operand Fun)
generateFunOp (Global g) _ _ = return $ global g
generateFunOp e retDir argDirs = do
  funVar <- generateExpr (Just "1") e
  funInt <- loadVar "func-int" funVar
  funPtr <- "func-ptr" =: intToPtr funInt
  "func" =: bitcastToFun funPtr retDir argDirs

generateGlobal :: Name -> Gen Var
generateGlobal g = do
  mdef <- asks (($ g) . signatures)
  case mdef of
    Just (Converted.Constant Direct _) ->
      return $ IndirectVar $ global g
    Just (Converted.Constant Indirect _) -> do
      ptr <- "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (Converted.Function retDir args _) -> return
      $ DirectVar
      $ ptrToIntExpr
      $ bitcastFunToPtrExpr (global g) retDir $ teleAnnotations args
    _ -> return $ DirectVar $ global g

generateBranches
  :: Expr Var
  -> Branches QConstr () Expr Var
  -> (Expr Var -> Gen a)
  -> Gen [(a, LLVM.Operand Label)]
generateBranches caseExpr branches brCont = do
  postLabel <- LLVM.Operand <$> freshenName "after-branch"
  case branches of
    ConBranches [] _ -> mdo
      void $ generateExpr Nothing caseExpr
      emit unreachable
      return []
    ConBranches [(Builtin.Ref, tele, brScope)] _ -> mdo
      exprInt <- loadVar "case-expr-int" =<< generateExpr Nothing caseExpr
      expr <- "case-expr" =: intToPtr exprInt
      branchLabel <- LLVM.Operand <$> freshenName Builtin.RefName

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele $ pure <$> Vector.fromList (reverse revArgs)
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateExpr (Just "1") $ inst s
                szInt <- loadVar "size" sz
                "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    ConBranches [(QConstr _ c, tele, brScope)] _ -> mdo
      expr <- indirect "case-expr" =<< generateExpr Nothing caseExpr
      branchLabel <- LLVM.Operand <$> freshenName c

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele $ pure <$> Vector.fromList (reverse revArgs)
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateExpr (Just "1") $ inst s
                szInt <- loadVar "size" sz
                "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, branchLabel)]

    ConBranches cbrs _ -> do
      expr <- indirect "case-expr" =<< generateExpr Nothing caseExpr
      e0Ptr <- "tag-pointer" =: getElementPtr expr "0"
      e0 <- "tag" =: load e0Ptr

      branchLabels <- Traversable.forM cbrs $ \(qc@(QConstr _ c), _, _) -> do
        Just qcIndex <- constrIndex qc
        branchLabel <- LLVM.Operand <$> freshenName c
        return (qcIndex, branchLabel)

      failLabel <- LLVM.Operand <$> freshenName "pattern-match-failed"
      emit $ switch e0 failLabel branchLabels

      contResults <- Traversable.forM (zip cbrs branchLabels) $ \((_, tele, brScope), (_, branchLabel)) -> mdo
        emitLabel branchLabel

        let teleVector = Vector.indexed $ unTelescope tele
            inst = instantiateTele $ pure <$> Vector.fromList (reverse revArgs)
            go (vs, index) (i, (h, (), s)) = do
              ptr <- h =: getElementPtr expr index
              nextIndex <- if i == Vector.length teleVector - 1
                then return index
                else do
                  sz <- generateExpr (Just "1") $ inst s
                  szInt <- loadVar "size" sz
                  "index" =: add index szInt
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

    LitBranches lbrs def -> do
      e0 <- loadVar "lit" =<< generateExpr (Just "1") caseExpr

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
      v <- generateExpr (Just "1") o
      unOperand <$> loadVar mempty v
  ret <- "prim" =: Instr (Foldable.fold strs)
  return $ DirectVar ret

generateConstant :: Visibility -> Name -> Constant Var -> Gen B
generateConstant visibility name (Constant dir e) = do
  let gname = unOperand $ global name
      initName = gname <> "-init"
      vis | visibility == Private = "private"
          | otherwise = ""
  emitRaw $ Instr $ gname <+> "= global" <+> vis <+> typVal <> ", align" <+> align
  emitRaw $ Instr ""
  emitRaw $ Instr $ "define private fastcc" <+> voidT <+> initName <> "() {"
  case dir of
    Void -> storeExpr Nothing e $ global name
    Direct -> storeExpr Nothing e $ global name
    Indirect -> do
      ptr <- gcAllocExpr e
      emit $ storePtr ptr $ global name
  emit returnVoid
  emitRaw "}"
  return $ "  call fastcc" <+> voidT <+> initName <> "()"
  where
    typVal = case dir of
      Void -> pointer "null"
      Direct -> integer "0"
      Indirect -> pointer "null"

generateFunction :: Visibility -> Name -> Function Var -> Gen ()
generateFunction visibility name (Function retDir hs funScope) = do
  vs <- Traversable.forM hs $ \(h, d) -> do
    n <- freshWithHint h
    return $ case d of
      Void -> VoidVar
      Direct -> DirectVar $ LLVM.Operand n
      Indirect -> IndirectVar $ LLVM.Operand n
  let funExpr = instantiateTele (pure <$> vs) funScope
      vis | visibility == Private = "private"
          | otherwise = ""
  case retDir of
    Void -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      storeExpr Nothing funExpr $ LLVM.Operand "null"
      emit returnVoid
    Indirect -> do
      ret <- LLVM.Operand <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeExpr Nothing funExpr ret
      emit returnVoid
    Direct -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> integerT <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr Nothing funExpr
      resInt <- loadVar "function-result" res
      emit $ returnInt resInt
  emitRaw "}"
  where
    go VoidVar = []
    go (DirectVar n) = [integer n]
    go (IndirectVar n) = [pointer n]

generateDefinition :: Name -> Definition Var -> Gen B
generateDefinition name def = case def of
  ConstantDef v c -> generateConstant v name c
  FunctionDef v f -> do
    generateFunction v name f
    return mempty
