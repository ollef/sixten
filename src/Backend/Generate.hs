{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module Backend.Generate where

import qualified Bound
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.Foldable as Foldable
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Backend.LLVM
import Backend.Target
import Builtin
import Syntax.Annotation
import Syntax.Branches
import Syntax.Direction
import Syntax.Hint
import Syntax.Name
import Syntax.Primitive
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Converted as Converted
import Syntax.Sized.Lifted
import Syntax.Telescope
import Util

-------------------------------------------------------------------------------
-- Generation environment
data GenEnv = GenEnv
  { constrArity :: QConstr -> Maybe Int
  , signatures :: Name -> Maybe (Converted.Signature Converted.Expr Closed.Expr Void)
  , returnDirections :: Name -> Maybe RetDir
  }

type Gen = ReaderT GenEnv (State LLVMState)

runGen :: GenEnv -> Gen a -> Target -> (a, [B])
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
  => C
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
generateExpr :: Gen (Operand Int) -> Expr RetDir Var -> Gen Var
generateExpr genSz expr = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit l -> return $ DirectVar $ shower l
  Con qc es -> do
    sz <- genSz
    generateCon sz qc es
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedExpr) es
    case retDir of
      ReturnVoid -> do
        emit $ varCall voidT fun args
        return VoidVar
      ReturnIndirect OutParam -> do
        sz <- genSz
        ret <- "call-return" =: alloca sz
        emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
        return $ IndirectVar ret
      ReturnIndirect Projection -> do
        ret <- "call-return" =: varCall pointerT fun args
        return $ IndirectVar ret
      ReturnDirect -> do
        ret <- "call-return" =: varCall integerT fun args
        return $ DirectVar ret
  Let _h e s -> do
    v <- generateExpr (error "generateExpr sz") e
    generateExpr genSz $ Bound.instantiate1 (pure v) s
  Case e brs -> mdo
    rets <- generateBranches e brs $ \br -> do
      v <- generateExpr genSz br
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
    case (rets, mdirectRets) of
      ([], _) -> return $ IndirectVar undef
      (_, Just directRets) -> fmap DirectVar $ "case-result" =: phiInt directRets
      (_, Nothing) -> fmap IndirectVar $ "case-result" =: phiPtr (first snd <$> rets)
  Prim p -> generatePrim p
  Anno e typ -> do
    let genSz' = do
          szVar <- generateExpr generateTypeSize typ
          loadVar "size" szVar
    generateExpr genSz' e

storeExpr :: Gen (Operand Int) -> Expr RetDir Var -> Operand Ptr -> Gen ()
storeExpr genSz expr ret = case expr of
  Var v -> do
    sz <- genSz
    varcpy ret v sz
  Global g -> do
    sz <- genSz
    v <- generateGlobal g
    varcpy ret v sz
  Lit l -> emit $ store (shower l) ret
  Con qc es -> storeCon qc es ret
  Call retDir funExpr es -> do
    fun <- generateFunOp funExpr retDir $ snd <$> es
    args <- mapM (uncurry generateDirectedExpr) es
    case retDir of
      ReturnVoid -> emit $ varCall voidT fun args
      ReturnIndirect OutParam -> emit $ varCall voidT fun $ Vector.snoc args $ IndirectVar ret
      ReturnIndirect Projection -> do
        res <- "call-return" =: varCall pointerT fun args
        sz <- genSz
        wordcpy ret res sz
      ReturnDirect -> do
        res <- "call-return" =: varCall integerT fun args
        emit $ store res ret
  Let _h e s -> do
    v <- generateExpr (error "storeExpr sz") e
    storeExpr genSz (Bound.instantiate1 (pure v) s) ret
  Case e brs -> void $ generateBranches e brs $ \br -> storeExpr genSz br ret
  Prim p -> do
    res <- generatePrim p
    intRes <- loadVar "loaded-prim" res
    emit $ store intRes ret
  Anno e typ -> do
    let genSz' = do
          szVar <- generateExpr generateTypeSize typ
          loadVar "size" szVar
    storeExpr genSz' e ret

generateIntSize :: Gen (Operand Int)
generateIntSize = do
  v <- generateExpr generateTypeSize $ Global Builtin.IntName
  loadVar "size" v

generateTypeSize :: Gen (Operand Int)
generateTypeSize = do
  v <- generateExpr generateTypeSize $ Global Builtin.TypeName
  loadVar "size" v

generatePiSize :: Gen (Operand Int)
generatePiSize = do
  v <- generateExpr generateTypeSize $ Global Builtin.PiTypeName
  loadVar "size" v

generateDirectedExpr
  :: Expr RetDir Var
  -> Direction
  -> Gen Var
generateDirectedExpr expr dir
  = generateExpr (error "generateDirectedExpr sz") expr >>= directed dir

gcAllocExpr :: Expr RetDir Var -> Gen (Operand Ptr)
gcAllocExpr (Anno expr typ) = do
  szVar <- generateExpr generateTypeSize typ
  szInt <- loadVar "size" szVar
  ref <- gcAlloc szInt
  storeExpr (pure szInt) expr ref
  return ref
gcAllocExpr _ = error "gcAllocExpr"

generateCon :: Operand Int -> QConstr -> Vector (Expr RetDir Var) -> Gen Var
generateCon _ Builtin.Ref es = do
  sizes <- mapM (loadVar "size" <=< generateExpr generateIntSize . sizeOf) es
  (is, fullSize) <- adds sizes
  ref <- gcAlloc fullSize
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es) $ \(sz, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ref i
    storeExpr (pure sz) e index
  refInt <- "ref-int" =: ptrToInt ref
  return $ DirectVar refInt
generateCon sz qc es = do
  ret <- "cons-cell" =: alloca sz
  storeCon qc es ret
  return $ IndirectVar ret

storeCon :: QConstr -> Vector (Expr RetDir Var) -> Operand Ptr -> Gen ()
storeCon Builtin.Ref es ret = do
  v <- generateCon "1" Builtin.Ref es
  i <- loadVar mempty v
  emit $ store i ret
storeCon qc es ret = do
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . sized 1 . Lit . fromIntegral) mqcIndex es
  sizes <- mapM (loadVar "size" <=< generateExpr generateIntSize . sizeOf) es'
  (is, _) <- adds sizes
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es') $ \(sz, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ret i
    storeExpr (pure sz) e index

generateFunOp :: Expr RetDir Var -> RetDir -> Vector Direction -> Gen (Operand Fun)
generateFunOp (Global g) _ _ = return $ global g
generateFunOp e retDir argDirs = do
  funVar <- generateExpr generatePiSize e
  funInt <- loadVar "func-int" funVar
  funPtr <- "func-ptr" =: intToPtr funInt
  "func" =: bitcastToFun funPtr retDir argDirs

generateGlobal :: Name -> Gen Var
generateGlobal g = do
  mdef <- asks (($ g) . signatures)
  case mdef of
    Just (Converted.Constant Void _) -> return VoidVar
    Just (Converted.Constant Direct _) ->
      return $ IndirectVar $ global g
    Just (Converted.Constant Indirect _) -> do
      ptr <- "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (Converted.Function _ args _) -> do
      mretDir <- asks (($ g) . returnDirections)
      case mretDir of
        Nothing -> error "generateGlobal"
        Just retDir ->
          return
            $ DirectVar
            $ ptrToIntExpr
            $ bitcastFunToPtrExpr (global g) retDir $ teleAnnotations args
    _ -> return $ DirectVar $ global g

generateBranches
  :: Expr RetDir Var
  -> Branches QConstr () (Expr RetDir) Var
  -> (Expr RetDir Var -> Gen a)
  -> Gen [(a, Operand Label)]
generateBranches caseExpr branches brCont = do
  postLabel <- Operand . text <$> freshenName "after-branch"
  case branches of
    NoBranches _ -> do
      void $ generateExpr (error "generateBranches sz") caseExpr
      emit unreachable
      return []
    ConBranches ((Builtin.Ref, tele, brScope) NonEmpty.:| []) -> mdo
      exprInt <- loadVar "case-expr-int" =<< generateExpr (error "generateBranches Con sz") caseExpr
      expr <- "case-expr" =: intToPtr exprInt
      branchLabel <- Operand . text <$> freshenName Builtin.RefName

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele pure $ Vector.fromList (reverse revArgs)
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateExpr generateIntSize $ inst s
                szInt <- loadVar "size" sz
                "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      afterBranchLabel <- gets currentLabel
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, afterBranchLabel)]

    ConBranches ((QConstr _ (Constr constrName), tele, brScope) NonEmpty.:| []) -> mdo
      expr <- indirect "case-expr" =<< generateExpr (error "generateBranches single Con sz") caseExpr
      branchLabel <- Operand . text <$> freshenName constrName

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele pure $ Vector.fromList (reverse revArgs)
          go (vs, index) (i, (h, (), s)) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateExpr generateIntSize $ inst s
                szInt <- loadVar "size" sz
                "index" =: add index szInt
            return (IndirectVar ptr : vs, nextIndex)

      (revArgs, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      afterBranchLabel <- gets currentLabel
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, afterBranchLabel)]

    ConBranches cbrs -> do
      let cbrs' = NonEmpty.toList cbrs
      expr <- indirect "case-expr" =<< generateExpr (error "generateBranches ConBranches sz") caseExpr
      e0Ptr <- "tag-pointer" =: getElementPtr expr "0"
      e0 <- "tag" =: load e0Ptr

      branchLabels <- Traversable.forM cbrs' $ \(qc@(QConstr _ (Constr constrName)), _, _) -> do
        Just qcIndex <- constrIndex qc
        branchLabel <- Operand . text <$> freshenName constrName
        return (qcIndex, branchLabel)

      failLabel <- Operand . text <$> freshenName "pattern-match-failed"
      emit $ switch e0 failLabel branchLabels

      contResults <- Traversable.forM (zip cbrs' branchLabels) $ \((_, tele, brScope), (_, branchLabel)) -> mdo
        emitLabel branchLabel

        let teleVector = Vector.indexed $ unTelescope tele
            inst = instantiateTele pure $ Vector.fromList (reverse revArgs)
            go (vs, index) (i, (h, (), s)) = do
              ptr <- h =: getElementPtr expr index
              nextIndex <- if i == Vector.length teleVector - 1
                then return index
                else do
                  sz <- generateExpr generateIntSize $ inst s
                  szInt <- loadVar "size" sz
                  "index" =: add index szInt
              return (IndirectVar ptr : vs, nextIndex)

        (revArgs, _) <- Foldable.foldlM go (mempty, "1") teleVector
        contResult <- brCont $ inst brScope
        afterBranchLabel <- gets currentLabel
        emit $ branch postLabel
        return (contResult, afterBranchLabel)

      emitLabel failLabel
      emit unreachable
      emitLabel postLabel
      return contResults

    LitBranches lbrs def -> do
      let lbrs' = NonEmpty.toList lbrs
      e0 <- loadVar "lit" =<< generateExpr generateIntSize caseExpr

      branchLabels <- Traversable.forM lbrs' $ \(l, _) -> do
        branchLabel <- Operand . text <$> freshenName (shower l)
        return (fromIntegral l, branchLabel)

      defaultLabel <- Operand . text <$> freshenName "default"
      emit $ switch e0 defaultLabel branchLabels

      contResults <- Traversable.forM (zip lbrs' branchLabels) $ \((_, br), (_, brLabel)) -> do
        emitLabel brLabel
        contResult <- brCont br
        afterBranchLabel <- gets currentLabel
        emit $ branch postLabel
        return (contResult, afterBranchLabel)

      emitLabel defaultLabel
      defaultContResult <- brCont def
      afterDefaultLabel <- gets currentLabel
      emit $ branch postLabel
      emitLabel postLabel
      return $ (defaultContResult, afterDefaultLabel) : contResults

generatePrim
  :: Primitive (Expr RetDir Var)
  -> Gen Var
generatePrim (Primitive dir xs) = do
  strs <- forM xs $ \x -> case x of
    TextPart t -> return t
    VarPart o -> do
      v <- generateExpr generateIntSize o
      unOperand <$> loadVar mempty v
  let instr = Instr $ Foldable.fold strs
  case dir of
    Void -> do
      emit instr
      return $ VoidVar
    Direct -> do
      ret <- "prim" =: instr
      return $ DirectVar ret
    Indirect -> do
      ret <- "prim" =: instr
      return $ IndirectVar ret

generateConstant :: Visibility -> Name -> Constant (Expr RetDir) Var -> Gen C
generateConstant visibility name (Constant dir e) = do
  let gname = unOperand $ global name
      initName = unOperand $ global $ name <> "-init"
      vis | visibility == Private = "private"
          | otherwise = ""
  emitRaw $ Instr $ gname <+> "= unnamed_addr global" <+> vis <+> typVal <> ", align" <+> align
  emitRaw $ Instr ""
  emitRaw $ Instr $ "define private fastcc" <+> voidT <+> initName <> "() {"
  case dir of
    Void -> storeExpr (error "generateConstant Void sz") e $ global name
    Direct -> storeExpr (error "generateConstant Direct sz") e $ global name
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

generateFunction :: Visibility -> Name -> Function RetDir (Expr RetDir) Var -> Gen ()
generateFunction visibility name (Function retDir args funScope) = do
  vs <- forMTele args $ \h d _sz -> do
    n <- text <$> freshWithHint h
    return $ case d of
      Void -> VoidVar
      Direct -> DirectVar $ Operand n
      Indirect -> IndirectVar $ Operand n
  let funExpr = instantiateTele pure vs funScope
      vis | visibility == Private = "private"
          | otherwise = ""
  case retDir of
    ReturnVoid -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      storeExpr (error "generateFunction Void sz") funExpr $ Operand "null"
      emit returnVoid
    ReturnIndirect OutParam -> do
      ret <- Operand . text <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeExpr (error "generateFunction Out sz") funExpr ret
      emit returnVoid
    ReturnIndirect Projection -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> pointerT <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr (error "generateFunction Indirect sz") funExpr
      resPtr <- indirect "function-result" res
      emit $ returnPtr resPtr
    ReturnDirect -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> integerT <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr (error "generateFunction Direct sz") funExpr
      resInt <- loadVar "function-result" res
      emit $ returnInt resInt
  emitRaw "}"
  where
    go VoidVar = []
    go (DirectVar n) = [integer n]
    go (IndirectVar n) = [pointer n]

generateDefinition :: Name -> Definition RetDir (Expr RetDir) Var -> Gen C
generateDefinition name def = case def of
  ConstantDef v c -> generateConstant v name c
  FunctionDef v f -> do
    generateFunction v name f
    return mempty
