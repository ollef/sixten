{-# LANGUAGE DeriveFunctor, OverloadedStrings, RecursiveDo #-}
module Backend.Generate where

import qualified Bound
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Foldable as Foldable
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Word
import System.IO

import Backend.LLVM
import Backend.Target(Target)
import qualified Backend.Target as Target
import Builtin
import Paths_sixten
import Syntax.Annotation
import Syntax.Branches
import Syntax.Direction
import Syntax.Extern(Language)
import qualified Syntax.Extern as Extern
import Syntax.GlobalBind hiding (global)
import Syntax.Hint
import Syntax.Literal
import Syntax.Module
import Syntax.Name
import Syntax.Sized.Definition
import Syntax.Sized.Extracted as Extracted
import Syntax.Telescope
import Util
import Util.Tsil

-------------------------------------------------------------------------------
-- Generation environment
data GenEnv = GenEnv
  { constructorIndex :: QConstr -> Maybe Int
  , signatures :: QName -> Maybe (Signature ReturnIndirect)
  }

type Gen = ReaderT GenEnv (State LLVMState)

data Generated a = Generated
  { generated :: a
  , generatedCode :: Text
  } deriving (Functor)

runGen :: GenEnv -> Target -> Gen a -> Generated a
runGen env tgt m
  = uncurry Generated
  $ Text.unlines <$> runLLVM tgt (runReaderT m env)

constrIndex :: QConstr -> Gen (Maybe Int)
constrIndex qc = asks $ ($ qc) . constructorIndex

-------------------------------------------------------------------------------
-- Vars
data Var
  = VoidVar
  | IndirectVar (Operand Ptr)
  | DirectVar Size (Operand Direct)
  deriving Show

loadVar :: Size -> NameHint -> Var -> Gen (Operand Direct)
loadVar _ _ VoidVar = return "0"
loadVar sz _ (DirectVar sz' o)
  | sz == sz' = return o
  | otherwise = error "loadVar size mismatch"
loadVar sz h (IndirectVar o) = loadDirect sz h o

loadIntVar :: NameHint -> Var -> Gen (Operand Int)
loadIntVar h v = do
  intSize <- gets $ Target.intBytes . target
  directInt <$> loadVar intSize h v

loadByteVar :: NameHint -> Var -> Gen (Operand Word8)
loadByteVar h v = directByte <$> loadVar 1 h v

directInt :: Operand Direct -> Operand Int
directInt = Operand . unOperand

directByte :: Operand Direct -> Operand Word8
directByte = Operand . unOperand

intDirect :: Operand Int -> Operand Direct
intDirect = Operand . unOperand

indirect :: NameHint -> Var -> Gen (Operand Ptr)
indirect _ VoidVar = return "null"
indirect n (DirectVar sz o) = do
  result <- n =: alloca (Operand $ shower sz)
  storeDirect sz o result
  return result
indirect _ (IndirectVar o) = return o

varcpy :: Operand Ptr -> Var -> Operand Int -> Gen ()
varcpy _dst VoidVar _sz = return ()
varcpy dst (DirectVar sz src) _sz = storeDirect sz src dst
varcpy dst (IndirectVar src) sz = memcpy dst src sz

varCall
  :: (Foldable f, Functor f)
  => Maybe Language
  -> C
  -> Operand Fun
  -> f Var
  -> Instr a
varCall lang retType name xs = Instr
  $ "call" <+> cc <+> retType <+> unOperand name
  <> "(" <> Foldable.fold (intersperse ", " $ Foldable.toList $ concat $ go <$> xs) <> ")"
  where
    cc = case lang of
      Nothing -> "fastcc"
      Just Extern.C -> "ccc"
    go VoidVar = []
    go (DirectVar sz x) = [direct sz x]
    go (IndirectVar x) = [pointer x]

directed
  :: Alternative f
  => Direction
  -> Var
  -> Gen (f Var)
directed d v = case d of
  Direct 0 -> return empty
  Direct sz -> pure . DirectVar sz <$> loadVar sz mempty v
  Indirect -> pure . IndirectVar <$> indirect mempty v

-------------------------------------------------------------------------------
-- Generation
generateExpr :: Expr Var -> Expr Var -> Gen Var
generateExpr expr typ = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit (Integer l) -> do
    sz <- gets (Target.intBytes . target)
    return $ DirectVar sz $ shower l
  Lit (Byte l) ->
    return $ DirectVar 1 $ shower l
  Con qc es -> generateCon qc es typ
  Call funExpr es -> do
    (retDir, argDirs) <- funSignature funExpr $ Vector.length es
    generateCall Nothing retDir funExpr (Vector.zip argDirs es) typ
  PrimCall lang retDir funExpr es -> generateCall lang retDir funExpr es typ
  Let _h e s -> do
    v <- generateExpr e $ unknownSize "let"
    generateExpr (Bound.instantiate1 (pure v) s) typ
  Case e brs -> case typ of
    Lit (Integer sz) -> do
      rets <- generateBranches e brs $ \br -> do
        v <- generateExpr br typ
        loadVar sz "case-result" v
      case rets of
        [] -> return $ DirectVar sz undef
        _ -> fmap (DirectVar sz) $ "case-result" =: phiDirect sz rets
    _ -> do
      rets <- generateBranches e brs $ \br -> do
        v <- generateExpr br typ
        indirect mempty v
      case rets of
        [] -> return $ IndirectVar undef
        _ -> fmap IndirectVar $ "case-result" =: phiPtr rets
  Anno e typ' -> generateExpr e typ'

generateIntExpr :: Expr Var -> Gen (Operand Int)
generateIntExpr expr = do
  intSize <- gets $ Target.intBytes . target
  sizeVar <- generateExpr expr $ Lit $ Integer intSize
  loadIntVar "size" sizeVar

generateByteExpr :: Expr Var -> Gen (Operand Word8)
generateByteExpr expr = do
  sizeVar <- generateExpr expr $ Lit $ Integer 1
  loadByteVar "size" sizeVar

unknownSize :: Name -> Expr v
unknownSize n = Global $ unqualified $ "unknownSize." <> n

generateCall
  :: Maybe Language
  -> RetDir
  -> Expr Var
  -> Vector (Direction, Expr Var)
  -> Expr Var
  -> Gen Var
generateCall lang retDir funExpr es typ = do
  let argDirs = fst <$> es
  fun <- generateFunOp funExpr retDir argDirs
  args <- join <$> mapM (uncurry generateDirectedExpr) es
  case retDir of
    ReturnDirect 0 -> do
      emit $ varCall lang voidT fun args
      return VoidVar
    ReturnDirect sz -> do
      ret <- "call-return" =: varCall lang (directT sz) fun args
      return $ DirectVar sz ret
    ReturnIndirect OutParam -> do
      sz <- generateIntExpr typ
      ret <- "call-return" =: alloca sz
      emit $ varCall lang voidT fun $ Vector.snoc args $ IndirectVar ret
      return $ IndirectVar ret
    ReturnIndirect Projection -> do
      ret <- "call-return" =: varCall lang pointerT fun args
      return $ IndirectVar ret

storeExpr :: Expr Var -> Expr Var -> Operand Ptr -> Gen ()
storeExpr expr typ ret = case expr of
  Var v -> do
    sz <- generateIntExpr typ
    varcpy ret v sz
  Global g -> do
    sz <- generateIntExpr typ
    v <- generateGlobal g
    varcpy ret v sz
  Lit (Integer l) -> storeInt (shower l) ret
  Lit (Byte l) -> storeByte (shower l) ret
  Con qc es -> storeCon qc es ret
  Call funExpr es -> do
    (retDir, argDirs) <- funSignature funExpr $ Vector.length es
    storeCall Nothing retDir funExpr (Vector.zip argDirs es) typ ret
  PrimCall lang retDir funExpr es -> storeCall lang retDir funExpr es typ ret
  Let _h e s -> do
    v <- generateExpr e $ unknownSize "storeLet"
    storeExpr (Bound.instantiate1 (pure v) s) typ ret
  Case e brs -> void $ generateBranches e brs $ \br -> storeExpr br typ ret
  Anno e typ' -> storeExpr e typ' ret

storeCall
  :: Maybe Language
  -> RetDir
  -> Expr Var
  -> Vector (Direction, Expr Var)
  -> Expr Var
  -> Operand Ptr
  -> Gen ()
storeCall lang retDir funExpr es typ ret = do
  let argDirs = fst <$> es
  fun <- generateFunOp funExpr retDir argDirs
  args <- join <$> mapM (uncurry generateDirectedExpr) es
  case retDir of
    ReturnDirect 0 -> emit $ varCall lang voidT fun args
    ReturnDirect sz -> do
      res <- "call-return" =: varCall lang (directT sz) fun args
      storeDirect sz res ret
    ReturnIndirect OutParam -> emit $ varCall lang voidT fun $ Vector.snoc args $ IndirectVar ret
    ReturnIndirect Projection -> do
      res <- "call-return" =: varCall lang pointerT fun args
      sz <- generateIntExpr typ
      memcpy ret res sz

funSignature :: Expr Var -> Int -> Gen (RetDir, Vector Direction)
funSignature expr arity = case expr of
  Global g -> do
    msig <- asks (($ g) . signatures)
    return $ case msig of
      Just (FunctionSig retDir argDirs) -> (retDir, argDirs)
      _ -> def
  _ -> error "Generate.funSignature non-global"
  where
    def = (ReturnIndirect OutParam, Vector.replicate arity Indirect)

generateDirectedExpr
  :: Alternative f
  => Direction
  -> Expr Var
  -> Gen (f Var)
generateDirectedExpr dir expr
  = generateExpr expr (unknownSize "generateDirectedExpr") >>= directed dir

gcAllocExpr :: Expr Var -> Gen (Operand Ptr)
gcAllocExpr (Anno expr typ) = do
  sz <- generateIntExpr typ
  intSize <- gets $ Target.intBytes . target
  ref <- gcAlloc sz
  let typ' = case typ of
        Lit _ -> typ
        _ -> pure $ DirectVar intSize $ intDirect sz
  storeExpr expr typ' ref
  return ref
gcAllocExpr _ = error "gcAllocExpr"

generateCon :: QConstr -> Vector (Expr Var) -> Expr Var -> Gen Var
generateCon Builtin.Ref es _ = do
  sizes <- mapM (generateIntExpr . sizeOf) es
  (is, fullSize) <- adds sizes
  ref <- gcAlloc fullSize
  intSize <- gets $ Target.intBytes . target
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es) $ \(sz, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ref i
    storeExpr e (pure $ DirectVar intSize $ intDirect sz) index
  refInt <- "ref-int" =: ptrToInt ref
  ptrSize <- gets $ Target.ptrBytes . target
  return $ DirectVar ptrSize $ intDirect refInt
generateCon _ _ (Lit (Integer 0)) = return VoidVar
generateCon qc es typ = do
  sz <- generateIntExpr typ
  ret <- "cons-cell" =: alloca sz
  storeCon qc es ret
  return $ IndirectVar ret

storeCon :: QConstr -> Vector (Expr Var) -> Operand Ptr -> Gen ()
storeCon Builtin.Ref es ret = do
  ptrSize <- gets $ Target.ptrBytes . target
  v <- generateCon Builtin.Ref es $ Lit $ Integer ptrSize
  i <- loadVar ptrSize mempty v
  storeDirect ptrSize i ret
storeCon qc es ret = do
  intSize <- gets $ Target.intBytes . target
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . Sized (Lit $ Integer intSize) . Lit . Integer . fromIntegral) mqcIndex es
  sizes <- mapM (generateIntExpr . sizeOf) es'
  (is, _) <- adds sizes
  Foldable.forM_ (zip (Vector.toList sizes) $ zip is $ Vector.toList es') $ \(sz, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ret i
    storeExpr e (pure $ DirectVar intSize $ intDirect sz) index

generateFunOp :: Expr Var -> RetDir -> Vector Direction -> Gen (Operand Fun)
generateFunOp (Global g) _ _ = return $ global g
generateFunOp e retDir argDirs = do
  ptrSize <- gets $ Target.ptrBytes . target
  let piSize = ptrSize
  funVar <- generateExpr e $ Lit $ Integer piSize
  funInt <- loadVar ptrSize "func-int" funVar
  funPtr <- "func-ptr" =: intToPtr (directInt funInt)
  "func" =: bitcastToFun funPtr retDir argDirs

generateGlobal :: QName -> Gen Var
generateGlobal g = do
  msig <- asks (($ g) . signatures)
  ptrSize <- gets $ Target.ptrBytes . target
  case msig of
    Just (ConstantSig (Direct 0)) -> return VoidVar
    Just (ConstantSig (Direct sz)) ->
      return $ IndirectVar $ Operand $ "bitcast" <+> "(" <> directT sz <> "*" <+> unOperand (global g) <+> "to" <+> pointerT <> ")"
    Just (ConstantSig Indirect) -> do
      ptr <- "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (FunctionSig retDir args) -> return
      $ DirectVar ptrSize
      $ intDirect
      $ ptrToIntExpr
      $ bitcastFunToPtrExpr (global g) retDir args
    _ -> return $ IndirectVar $ global g

generateBranches
  :: Expr Var
  -> Branches QConstr () Expr Var
  -> (Expr Var -> Gen a)
  -> Gen [(a, Operand Label)]
generateBranches caseExpr branches brCont = do
  postLabel <- freshLabel "after-branch"
  intSize <- gets $ Target.intBytes . target
  case branches of
    ConBranches [] -> do
      void $ generateExpr caseExpr $ unknownSize "noBranches"
      emit unreachable
      return []
    ConBranches [ConBranch Builtin.Ref tele brScope] -> mdo
      exprInt <- loadVar intSize "case-expr-int" =<< generateExpr caseExpr (unknownSize "caseRef")
      expr <- "case-expr" =: intToPtr (directInt exprInt)
      branchLabel <- freshLabel $ fromQConstr Builtin.Ref

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele pure $ toVector args
          go (vs, index) (i, TeleArg h () s) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateIntExpr $ inst s
                "index" =: add index sz
            return (Snoc vs $ IndirectVar ptr, nextIndex)

      (args, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      afterBranchLabel <- gets currentLabel
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, afterBranchLabel)]

    ConBranches [ConBranch qc tele brScope] -> mdo
      expr <- indirect "case-expr" =<< generateExpr caseExpr (unknownSize "case-single")
      branchLabel <- freshLabel $ fromQConstr qc

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele pure $ toVector args
          go (vs, index) (i, TeleArg h () s) = do
            ptr <- h =: getElementPtr expr index
            nextIndex <- if i == Vector.length teleVector - 1
              then return index
              else do
                sz <- generateIntExpr $ inst s
                "index" =: add index sz
            return (Snoc vs $ IndirectVar ptr, nextIndex)

      (args, _) <- Foldable.foldlM go (mempty, "0") teleVector
      contResult <- brCont $ inst brScope
      afterBranchLabel <- gets currentLabel
      emit $ branch postLabel
      emitLabel postLabel
      return [(contResult, afterBranchLabel)]

    ConBranches cbrs -> do
      expr <- indirect "case-expr" =<< generateExpr caseExpr (unknownSize "conBranches")
      e0Ptr <- "tag-pointer" =: getElementPtr expr "0"
      e0 <- loadInt "tag" e0Ptr

      branchLabels <- Traversable.forM cbrs $ \(ConBranch qc _ _) -> do
        Just qcIndex <- constrIndex qc
        branchLabel <- freshLabel $ fromQConstr qc
        return (qcIndex, branchLabel)

      failLabel <- freshLabel "pattern-match-failed"
      emit $ switch e0 failLabel branchLabels

      contResults <- Traversable.forM (zip cbrs branchLabels) $ \(ConBranch _ tele brScope, (_, branchLabel)) -> mdo
        emitLabel branchLabel

        let teleVector = Vector.indexed $ unTelescope tele
            inst = instantiateTele pure $ toVector args
            go (vs, index) (i, TeleArg h () s) = do
              ptr <- h =: getElementPtr expr index
              nextIndex <- if i == Vector.length teleVector - 1
                then return index
                else do
                  sz <- generateIntExpr $ inst s
                  "index" =: add index sz
              return (Snoc vs $ IndirectVar ptr, nextIndex)

        (args, _) <- Foldable.foldlM go (mempty, shower intSize) teleVector
        contResult <- brCont $ inst brScope
        afterBranchLabel <- gets currentLabel
        emit $ branch postLabel
        return (contResult, afterBranchLabel)

      emitLabel failLabel
      emit unreachable
      emitLabel postLabel
      return contResults

    LitBranches lbrs@(LitBranch (Integer _) _ NonEmpty.:| _) def -> do
      let lbrs' = NonEmpty.toList lbrs
      e0 <- generateIntExpr caseExpr

      branchLabels <- Traversable.forM lbrs' $ \(LitBranch (Integer l) _) -> do
        branchLabel <- freshLabel $ shower l
        return (fromIntegral l, branchLabel)

      defaultLabel <- freshLabel "default"
      emit $ switch e0 defaultLabel branchLabels

      contResults <- Traversable.forM (zip lbrs' branchLabels) $ \(LitBranch _ br, (_, brLabel)) -> do
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

    LitBranches lbrs@(LitBranch (Byte _) _ NonEmpty.:| _) def -> do
      let lbrs' = NonEmpty.toList lbrs
      e0 <- generateByteExpr caseExpr

      branchLabels <- Traversable.forM lbrs' $ \(LitBranch (Byte l) _) -> do
        branchLabel <- freshLabel $ shower l
        return (l, branchLabel)

      defaultLabel <- freshLabel "default"
      emit $ switch8 e0 defaultLabel branchLabels

      contResults <- Traversable.forM (zip lbrs' branchLabels) $ \(LitBranch _ br, (_, brLabel)) -> do
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

generateConstant :: Visibility -> QName -> Constant Expr Var -> Gen C
generateConstant visibility name (Constant e) = do
  msig <- asks (($ name) . signatures)
  let gname = unOperand $ global name
      vis | visibility == Private = "private"
          | otherwise = ""
  case msig of
    Just (ConstantSig dir) ->
      case (e, dir) of
        (Anno (Lit (Integer l)) _, Direct sz) -> do
          emitRaw $ Instr $ gname <+> "=" <+> vis <+> "unnamed_addr constant" <+> direct sz (shower l) <> ", align" <+> align
          return mempty
        _ -> do
          let initName = "@" <> text (escape $ fromQName name <> "-init")
              typ = case dir of
                Indirect -> pointerT
                Direct 0 -> pointerT
                Direct sz -> directT sz
          emitRaw $ Instr $ gname <+> "=" <+> vis <+> "unnamed_addr global" <+> typ <+> "zeroinitializer, align" <+> align
          emitRaw $ Instr ""
          emitRaw $ Instr $ "define private fastcc" <+> voidT <+> initName <> "() {"
          case dir of
            Direct 0 -> void $ generateExpr e $ Lit $ Integer 0
            Direct sz -> storeExpr e (Lit $ Integer sz) $ Operand $ "bitcast" <+> "(" <> directT sz <> "*" <+> unOperand (global name) <+> "to" <+> pointerT <> ")"
            Indirect -> do
              ptr <- gcAllocExpr e
              emit $ storePtr ptr $ global name
          emit returnVoid
          emitRaw "}"
          return $ "  call fastcc" <+> voidT <+> initName <> "()"
    _ -> error "generateConstant"

generateFunction :: Visibility -> QName -> Function Expr Var -> Gen ()
generateFunction visibility name (Function args funScope) = do
  msig <- asks (($ name) . signatures)
  let (retDir, argDirs) = case msig of
        Just (FunctionSig rd ad) -> (rd, ad)
        _ -> error "generateFunction"
  vs <- iforMTele args $ \i h _ _sz -> do
    let d = argDirs Vector.! i
    n <- text <$> freshWithHint h
    return $ case d of
      Direct 0 -> VoidVar
      Direct sz -> DirectVar sz $ Operand n
      Indirect -> IndirectVar $ Operand n
  let funExpr = instantiateTele pure vs funScope
      vis | visibility == Private = "private"
          | otherwise = ""
  case retDir of
    ReturnDirect sz -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> directT sz <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr funExpr $ Lit $ Integer sz
      dres <- loadVar sz mempty res
      emit $ returnDirect sz dres
    ReturnIndirect OutParam -> do
      ret <- Operand . text <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeExpr funExpr (unknownSize "generateFunctionOutParam") ret
      emit returnVoid
    ReturnIndirect Projection -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> pointerT <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr funExpr $ unknownSize "generateFunctionProjection"
      resPtr <- indirect "function-result" res
      emit $ returnPtr resPtr
  emitRaw "}"
  where
    go VoidVar = []
    go (DirectVar sz n) = [direct sz n]
    go (IndirectVar n) = [pointer n]

generateDefinition :: QName -> Definition Expr Var -> Gen Text
generateDefinition name def = case def of
  ConstantDef v c -> do
    constantInt <- generateConstant v name c
    cfg <- gets config
    return $ unC constantInt cfg
  FunctionDef v _ f -> do
    generateFunction v name f
    return mempty
  AliasDef -> return mempty

generateDeclaration :: Declaration -> Gen ()
generateDeclaration decl
  = declareFun (declRetDir decl) (unqualified $ declName decl) (declArgDirs decl)

genSubmodule
  :: QName
  -> Extracted.Submodule (Definition Expr Var)
  -> Extracted.Submodule (Gen (Text, HashMap QName Text))
genSubmodule name modul = flip fmap modul $ \innards -> do
  unless (null $ submoduleDecls modul) $ do
    mapM_ generateDeclaration $ submoduleDecls modul
    emitRaw ""

  let globalDeps
        = HashSet.filter ((/= qnameModule name) . qnameModule)
        $ boundGlobals innards

  env <- ask
  tgt <- gets target

  let globs = flip map (HashSet.toList globalDeps) $ \g -> runGen env tgt $ do
        msig <- asks (($ g) . signatures)
        case msig of
          Just (FunctionSig retDir argDirs) -> declareFun retDir g argDirs
          Just (ConstantSig dir) -> declareConstant dir g
          Just (AliasSig _) -> return ()
          Nothing -> return ()
        return g

  def <- generateDefinition name innards
  return (def, HashMap.fromList $ (\g -> (generated g, generatedCode g)) <$> globs)

generateModule
  :: GenEnv
  -> Target
  -> QName
  -> Extracted.Submodule (Definition Expr Var)
  -> Extracted.Submodule (Generated (Text, HashMap QName Text))
generateModule env tgt x modul = runGen env tgt <$> genSubmodule x modul

writeLlvmModule
  :: ModuleName
  -> [Import]
  -> [Generated Text]
  -> HashMap QName Text
  -> Handle
  -> IO ()
writeLlvmModule mname imports gens decls handle = do
  let importedModules = HashSet.toList $ HashSet.fromList $ importModule <$> imports
  forwardDecls <- Text.readFile =<< getDataFileName "rts/forwarddecls.ll"
  let outputStrLn = Text.hPutStrLn handle
      outputNonEmpty s
        | Text.null s = return ()
        | otherwise = outputStrLn s
  outputStrLn forwardDecls
  forM_ (HashMap.elems decls) outputNonEmpty

  forM_ gens $ outputStrLn . generatedCode
  let initName mn = "@" <> escape (fromModuleName mn) <> "-init"
      initedName mn = "@" <> escape (fromModuleName mn) <> "-inited"
      thisInitName = initName mname
      thisInitedName = initedName mname

  forM_ importedModules $ \i ->
    outputStrLn $ "declare void " <> initName i <> "()"
  outputStrLn $ thisInitedName <> " = internal unnamed_addr global i1 false"
  outputStrLn ""
  outputStrLn $ "define void " <> thisInitName <> "() {"
  outputStrLn $ "  %isInited = load i1, i1* " <> thisInitedName
  outputStrLn "  switch i1 %isInited, label %not-inited [i1 true, label %inited]"
  outputStrLn "inited:"
  outputStrLn "  ret void"
  outputStrLn "not-inited:"
  outputStrLn "  call void @GC_init()"
  outputStrLn $ "  store i1 1, i1* " <> thisInitedName
  forM_ importedModules $ \i ->
    outputStrLn $ "  call void " <> initName i <> "()"
  forM_ gens $ outputNonEmpty . generated
  outputStrLn "  ret void"
  outputStrLn "}"
  outputStrLn ""

  outputStrLn "%\"global ctor\" = type { i32, void ()*, i8* }"
  outputStrLn $ "@llvm.global_ctors = appending global [1 x %\"global ctor\"] [%\"global ctor\" { i32 610, void ()* " <> thisInitName <> ", i8* null }]"

  when (mname == "Main") $ do
    outputStrLn ""
    outputStrLn "define i32 @main() {"
    -- TODO
    outputStrLn "  ret i32 0"
    outputStrLn "}"
