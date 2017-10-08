{-# LANGUAGE DeriveFunctor, FlexibleContexts, OverloadedStrings, RecursiveDo #-}
module Backend.Generate where

import qualified Bound
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import qualified Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
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
import qualified Builtin.Names as Builtin
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
import qualified TypeRep
import TypeRep(TypeRep)
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
  } deriving (Show, Functor)

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
  | DirectVar TypeRep (Operand Direct)
  deriving Show

loadVar :: TypeRep -> NameHint -> Var -> Gen (Operand Direct)
loadVar _ _ VoidVar = return "0"
loadVar rep _ (DirectVar rep' o)
  | rep == rep' = return o
  | otherwise = error "loadVar size mismatch"
loadVar rep h (IndirectVar o) = loadDirect rep h o

loadIntVar :: NameHint -> Var -> Gen (Operand Int)
loadIntVar h v = do
  intRep <- gets $ TypeRep.intRep . target
  directIntOperand <$> loadVar intRep h v

loadByteVar :: NameHint -> Var -> Gen (Operand Word8)
loadByteVar h v = directByteOperand <$> loadVar TypeRep.ByteRep h v

loadTypeVar :: NameHint -> Var -> Gen (Operand TypeRep)
loadTypeVar h v = do
  typeRep <- gets $ TypeRep.typeRep . target
  directTypeOperand <$> loadVar typeRep h v

directIntOperand :: Operand Direct -> Operand Int
directIntOperand = Operand . unOperand

directByteOperand :: Operand Direct -> Operand Word8
directByteOperand = Operand . unOperand

directTypeOperand :: Operand Direct -> Operand TypeRep
directTypeOperand = Operand . unOperand

intDirect :: Operand Int -> Operand Direct
intDirect = Operand . unOperand

typeDirect :: Operand TypeRep -> Operand Direct
typeDirect = Operand . unOperand

indirect :: NameHint -> Var -> Gen (Operand Ptr)
indirect _ VoidVar = return "null"
indirect n (DirectVar rep o) = do
  result <- n =: alloca (Operand $ shower $ TypeRep.size rep)
  storeDirect rep o result
  return result
indirect _ (IndirectVar o) = return o

varcpy :: Operand Ptr -> Var -> Operand Int -> Gen ()
varcpy _dst VoidVar _sz = return ()
varcpy dst (DirectVar rep src) _sz = storeDirect rep src dst
varcpy dst (IndirectVar src) rep = memcpy dst src rep

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
    go (DirectVar rep x) = [direct rep x]
    go (IndirectVar x) = [pointer x]

directed
  :: Alternative f
  => Direction
  -> Var
  -> Gen (f Var)
directed d v = case d of
  Direct TypeRep.UnitRep -> return empty
  Direct rep -> pure . DirectVar rep <$> loadVar rep mempty v
  Indirect -> pure . IndirectVar <$> indirect mempty v

-------------------------------------------------------------------------------
-- Generation
generateExpr :: Expr Var -> Expr Var -> Gen Var
generateExpr expr typ = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit (Integer l) -> do
    intRep <- gets $ TypeRep.intRep . target
    return $ DirectVar intRep $ shower l
  Lit (Byte l) ->
    return $ DirectVar TypeRep.ByteRep $ shower l
  Lit (TypeRep rep) -> do
    typeRep <- gets $ TypeRep.typeRep . target
    return $ DirectVar typeRep $ shower $ TypeRep.size rep
  Con qc es -> generateCon qc es typ
  Call funExpr es -> do
    (retDir, argDirs) <- funSignature funExpr $ Vector.length es
    generateCall Nothing retDir funExpr (Vector.zip argDirs es) typ
  PrimCall lang retDir funExpr es -> generateCall lang retDir funExpr es typ
  Let _h e s -> do
    v <- generateExpr e $ unknownSize "let"
    generateExpr (Bound.instantiate1 (pure v) s) typ
  Case e brs -> case typ of
    MkType rep -> do
      rets <- generateBranches e brs $ \br -> do
        v <- generateExpr br typ
        loadVar rep "case-result" v
      case rets of
        [] -> return $ DirectVar rep undef
        _ -> fmap (DirectVar rep) $ "case-result" =: phiDirect rep rets
    _ -> do
      rets <- generateBranches e brs $ \br -> do
        v <- generateExpr br typ
        indirect mempty v
      case rets of
        [] -> return $ IndirectVar undef
        _ -> fmap IndirectVar $ "case-result" =: phiPtr rets
  Anno e typ' -> generateExpr e typ'

generateTypeExpr :: Expr Var -> Gen (Operand TypeRep)
generateTypeExpr (MkType rep) = return (shower $ TypeRep.size rep)
generateTypeExpr expr = do
  typeRep <- gets $ TypeRep.typeRep . target
  repVar <- generateExpr expr $ Lit $ TypeRep typeRep
  loadTypeVar "typeRep" repVar

generateTypeSize :: Expr Var -> Gen (Operand TypeRep, Operand Int)
generateTypeSize (MkType rep) = return (shower $ TypeRep.size rep, shower $ TypeRep.size rep)
generateTypeSize typ = do
  rep <- generateTypeExpr typ
  size <- generateSizeOf rep
  return (rep, size)

generateSizeOf :: Operand TypeRep -> Gen (Operand Int)
generateSizeOf rep = do
  typeRep <- gets $ TypeRep.typeRep . target
  generateIntExpr
    $ Call (Global Builtin.SizeOfName)
    $ pure $ pure $ DirectVar typeRep $ typeDirect rep

generateIntExpr :: Expr Var -> Gen (Operand Int)
generateIntExpr expr = do
  intRep <- gets $ TypeRep.intRep . target
  sizeVar <- generateExpr expr $ Lit $ TypeRep intRep
  loadIntVar "size" sizeVar

generateByteExpr :: Expr Var -> Gen (Operand Word8)
generateByteExpr expr = do
  sizeVar <- generateExpr expr $ Lit $ TypeRep TypeRep.ByteRep
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
    ReturnDirect TypeRep.UnitRep -> do
      emit $ varCall lang voidT fun args
      return VoidVar
    ReturnDirect rep -> do
      ret <- "call-return" =: varCall lang (directT rep) fun args
      return $ DirectVar rep ret
    ReturnIndirect OutParam -> do
      (_, sz) <- generateTypeSize typ
      ret <- "call-return" =: alloca sz
      emit $ varCall lang voidT fun $ Vector.snoc args $ IndirectVar ret
      return $ IndirectVar ret
    ReturnIndirect Projection -> do
      ret <- "call-return" =: varCall lang pointerT fun args
      return $ IndirectVar ret

storeExpr :: Expr Var -> Expr Var -> Operand Ptr -> Gen ()
storeExpr expr typ ret = case expr of
  Var v -> do
    (_, sz) <- generateTypeSize typ
    varcpy ret v sz
  Global g -> do
    (_, sz) <- generateTypeSize typ
    v <- generateGlobal g
    varcpy ret v sz
  Lit (Integer l) -> storeInt (shower l) ret
  Lit (Byte l) -> storeByte (shower l) ret
  Lit (TypeRep l) -> storeInt (shower $ TypeRep.size l) ret
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
    ReturnDirect TypeRep.UnitRep -> emit $ varCall lang voidT fun args
    ReturnDirect rep -> do
      res <- "call-return" =: varCall lang (directT rep) fun args
      storeDirect rep res ret
    ReturnIndirect OutParam -> emit $ varCall lang voidT fun $ Vector.snoc args $ IndirectVar ret
    ReturnIndirect Projection -> do
      res <- "call-return" =: varCall lang pointerT fun args
      (_, sz) <- generateTypeSize typ
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
  rep <- generateTypeExpr typ
  typeRep <- gets $ TypeRep.typeRep . target
  sz <- generateSizeOf rep
  ref <- gcAlloc sz
  let typ' = case typ of
        Lit _ -> typ
        _ -> pure $ DirectVar typeRep $ typeDirect rep
  storeExpr expr typ' ref
  return ref
gcAllocExpr _ = error "gcAllocExpr"

productOffsets
  :: Foldable f
  => f (Operand TypeRep)
  -> Gen ([Operand Int], Operand TypeRep)
productOffsets = fmap (first Foldable.toList) . Foldable.foldlM go (Nil, "0")
  where
    go (indices, fullRep) rep = do
      typeRep <- gets $ TypeRep.typeRep . target
      fullRep' <- generateTypeExpr
        $ Call (Global Builtin.ProductTypeRepName)
        $ Vector.fromList
          [ pure $ DirectVar typeRep $ typeDirect fullRep
          , pure $ DirectVar typeRep $ typeDirect rep
          ]
      index <- generateSizeOf fullRep
      return (Snoc indices index, fullRep')

productOffsets'
  :: Vector (Operand TypeRep)
  -> Gen [Operand Int]
productOffsets' xs = fmap (Foldable.toList . fst) $ Foldable.foldlM go (Nil, "0") $ indexed xs
  where
    go (indices, fullRep) (i, rep) = do
      typeRep <- gets $ TypeRep.typeRep . target
      fullRep' <- if i == Vector.length xs - 1
        then return fullRep
        else generateTypeExpr
          $ Call (Global Builtin.ProductTypeRepName)
          $ Vector.fromList
            [ pure $ DirectVar typeRep $ typeDirect fullRep
            , pure $ DirectVar typeRep $ typeDirect rep
            ]
      index <- generateSizeOf fullRep
      return (Snoc indices index, fullRep')

generateCon :: QConstr -> Vector (Expr Var) -> Expr Var -> Gen Var
generateCon Builtin.Ref es _ = do
  reps <- mapM (generateTypeExpr . typeOf) es
  (is, fullRep) <- productOffsets reps
  fullSize <- generateSizeOf fullRep
  ref <- gcAlloc fullSize
  typeRep <- gets $ TypeRep.typeRep . target
  Foldable.forM_ (zip (Vector.toList reps) $ zip is $ Vector.toList es) $ \(rep, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ref i
    storeExpr e (pure $ DirectVar typeRep $ typeDirect rep) index
  refInt <- "ref-int" =: ptrToInt ref
  ptrRep <- gets $ TypeRep.ptrRep . target
  return $ DirectVar ptrRep $ intDirect refInt
generateCon _ _ (MkType TypeRep.UnitRep) = return VoidVar
generateCon qc es typ = do
  (_, sz) <- generateTypeSize typ
  ret <- "cons-cell" =: alloca sz
  storeCon qc es ret
  return $ IndirectVar ret

storeCon :: QConstr -> Vector (Expr Var) -> Operand Ptr -> Gen ()
storeCon Builtin.Ref es ret = do
  ptrRep <- gets $ TypeRep.ptrRep . target
  v <- generateCon Builtin.Ref es $ Lit $ TypeRep ptrRep
  i <- loadVar ptrRep mempty v
  storeDirect ptrRep i ret
storeCon qc es ret = do
  intRep <- gets $ TypeRep.intRep . target
  typeRep <- gets $ TypeRep.typeRep . target
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . Sized (Lit $ TypeRep intRep) . Lit . Integer . fromIntegral) mqcIndex es
  reps <- mapM (generateTypeExpr . typeOf) es'
  is <- productOffsets' reps
  Foldable.forM_ (zip (Vector.toList reps) $ zip is $ Vector.toList es') $ \(rep, (i, Anno e _)) -> do
    index <- "index" =: getElementPtr ret i
    storeExpr e (pure $ DirectVar typeRep $ typeDirect rep) index

generateFunOp :: Expr Var -> RetDir -> Vector Direction -> Gen (Operand Fun)
generateFunOp (Global g) _ _ = return $ global g
generateFunOp e retDir argDirs = do
  piRep <- gets $ TypeRep.piRep . target
  funVar <- generateExpr e $ Lit $ TypeRep piRep
  funInt <- loadVar piRep "func-int" funVar
  funPtr <- "func-ptr" =: intToPtr (directIntOperand funInt)
  "func" =: bitcastToFun funPtr retDir argDirs

generateGlobal :: QName -> Gen Var
generateGlobal g = do
  msig <- asks (($ g) . signatures)
  ptrRep <- gets $ TypeRep.ptrRep . target
  case msig of
    Just (ConstantSig (Direct TypeRep.UnitRep)) -> return VoidVar
    Just (ConstantSig (Direct rep)) ->
      return $ IndirectVar $ Operand $ "bitcast" <+> "(" <> directT rep <> "*" <+> unOperand (global g) <+> "to" <+> pointerT <> ")"
    Just (ConstantSig Indirect) -> do
      ptr <- "global" =: loadPtr (global g)
      return $ IndirectVar ptr
    Just (FunctionSig retDir args) -> return
      $ DirectVar ptrRep
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
  tgt <- gets target
  let intRep = TypeRep.intRep tgt
      typeRep = TypeRep.typeRep tgt
  case branches of
    ConBranches [] -> do
      void $ generateExpr caseExpr $ unknownSize "noBranches"
      emit unreachable
      return []
    ConBranches [ConBranch Builtin.Ref tele brScope] -> mdo
      exprInt <- loadVar intRep "case-expr-int" =<< generateExpr caseExpr (unknownSize "caseRef")
      expr <- "case-expr" =: intToPtr (directIntOperand exprInt)
      branchLabel <- freshLabel $ fromQConstr Builtin.Ref

      emit $ branch branchLabel
      emitLabel branchLabel
      let teleVector = Vector.indexed $ unTelescope tele
          inst = instantiateTele pure $ toVector args
          go (vs, fullRep) (i, TeleArg h () s) = do
            index <- generateIntExpr
              $ Call (Global Builtin.SizeOfName)
              $ pure $ pure $ DirectVar typeRep $ typeDirect fullRep
            ptr <- h =: getElementPtr expr index
            fullRep' <- if i == Vector.length teleVector - 1
              then return fullRep
              else do
                rep <- generateTypeExpr $ inst s
                generateTypeExpr
                  $ Call (Global Builtin.ProductTypeRepName)
                  $ Vector.fromList
                    [ pure $ DirectVar typeRep $ typeDirect fullRep
                    , pure $ DirectVar typeRep $ typeDirect rep
                    ]
            return (Snoc vs $ IndirectVar ptr, fullRep')

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
          go (vs, fullRep) (i, TeleArg h () s) = do
            index <- generateIntExpr
              $ Call (Global Builtin.SizeOfName)
              $ pure $ pure $ DirectVar typeRep $ typeDirect fullRep
            ptr <- h =: getElementPtr expr index
            fullRep' <- if i == Vector.length teleVector - 1
              then return fullRep
              else do
                rep <- generateTypeExpr $ inst s
                generateTypeExpr
                  $ Call (Global Builtin.ProductTypeRepName)
                  $ Vector.fromList
                    [ pure $ DirectVar typeRep $ typeDirect fullRep
                    , pure $ DirectVar typeRep $ typeDirect rep
                    ]
            return (Snoc vs $ IndirectVar ptr, fullRep')

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
            go (vs, fullRep) (i, TeleArg h () s) = do
              index <- generateIntExpr
                $ Call (Global Builtin.SizeOfName)
                $ pure $ pure $ DirectVar typeRep $ typeDirect fullRep
              ptr <- h =: getElementPtr expr index
              fullRep' <- if i == Vector.length teleVector - 1
                then return fullRep
                else do
                  rep <- generateTypeExpr $ inst s
                  generateTypeExpr
                    $ Call (Global Builtin.ProductTypeRepName)
                    $ Vector.fromList
                      [ pure $ DirectVar typeRep $ typeDirect fullRep
                      , pure $ DirectVar typeRep $ typeDirect rep
                      ]
              return (Snoc vs $ IndirectVar ptr, fullRep')

        (args, _) <- Foldable.foldlM go (mempty, shower $ TypeRep.size intRep) teleVector
        contResult <- brCont $ inst brScope
        afterBranchLabel <- gets currentLabel
        emit $ branch postLabel
        return (contResult, afterBranchLabel)

      emitLabel failLabel
      emit unreachable
      emitLabel postLabel
      return contResults

    LitBranches lbrs@(LitBranch firstLit _ NonEmpty.:| _) def -> do
      let lbrs' = NonEmpty.toList lbrs

      branchLabels <- Traversable.forM lbrs' $ \(LitBranch lit _) -> do
        branchLabel <- freshLabel $ shower lit
        return (lit, branchLabel)

      defaultLabel <- freshLabel "default"

      case firstLit of
        Integer _ -> do
          e0 <- generateIntExpr caseExpr
          emit
            $ switch e0 defaultLabel
            $ first (\(Integer i) -> fromIntegral i) <$> branchLabels
        Byte _ -> do
          e0 <- generateByteExpr caseExpr
          emit
            $ switch8 e0 defaultLabel
            $ first (\(Byte b) -> b) <$> branchLabels
        TypeRep _ -> do
          e0 <- generateIntExpr caseExpr -- should really be generateTypeExpr
          emit
            $ switch e0 defaultLabel
            $ first (\(TypeRep rep) -> fromIntegral $ TypeRep.size rep) <$> branchLabels

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
      directLit l rep = do
        emitRaw $ Instr $ gname <+> "=" <+> vis <+> "unnamed_addr constant" <+> direct rep (shower l) <> ", align" <+> align
        return mempty
  case msig of
    Just (ConstantSig dir) ->
      case (e, dir) of
        (Anno (Lit lit) _, Direct rep) -> case lit of
          Byte b -> directLit b rep
          Integer i -> directLit i rep
          TypeRep t -> directLit (TypeRep.size t) rep
        _ -> do
          let initName = "@" <> text (escape $ fromQName name <> "-init")
              typ = case dir of
                Indirect -> pointerT
                Direct TypeRep.UnitRep -> pointerT
                Direct rep -> directT rep
          emitRaw $ Instr $ gname <+> "=" <+> vis <+> "unnamed_addr global" <+> typ <+> "zeroinitializer, align" <+> align
          emitRaw $ Instr ""
          emitRaw $ Instr $ "define private fastcc" <+> voidT <+> initName <> "() {"
          case dir of
            Direct TypeRep.UnitRep -> void $ generateExpr e $ Lit $ TypeRep TypeRep.UnitRep
            Direct rep -> storeExpr e (Lit $ TypeRep rep) $ Operand $ "bitcast" <+> "(" <> directT rep <> "*" <+> unOperand (global name) <+> "to" <+> pointerT <> ")"
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
      Direct TypeRep.UnitRep -> VoidVar
      Direct rep -> DirectVar rep $ Operand n
      Indirect -> IndirectVar $ Operand n
  let funExpr = instantiateTele pure vs funScope
      vis | visibility == Private = "private"
          | otherwise = ""
  case retDir of
    ReturnDirect rep -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> directT rep <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr funExpr $ Lit $ TypeRep $ rep
      dres <- loadVar rep mempty res
      emit $ returnDirect rep dres
    ReturnIndirect OutParam -> do
      ret <- Operand . text <$> freshenName "return"
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> voidT <+> unOperand (global name)
        <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs <> pure (IndirectVar ret)) <> ") {"
      storeExpr funExpr (unknownSize "generateFunction OutParam") ret
      emit returnVoid
    ReturnIndirect Projection -> do
      emitRaw $ Instr $ "define" <+> vis <+> "fastcc" <+> pointerT <+> unOperand (global name) <> "(" <> Foldable.fold (intersperse ", " $ concat $ go <$> Vector.toList vs) <> ") {"
      res <- generateExpr funExpr $ unknownSize "generateFunction Projection"
      resPtr <- indirect "function-result" res
      emit $ returnPtr resPtr
  emitRaw "}"
  where
    go VoidVar = []
    go (DirectVar rep n) = [direct rep n]
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
        -- These may be emitted by the code generator, so are implicit
        -- dependencies of most code
        $ HashSet.insert Builtin.SizeOfName
        $ HashSet.insert Builtin.ProductTypeRepName
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
  outputStrLn $ "  store i1 1, i1* " <> thisInitedName
  outputStrLn "  call void @GC_init()"
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
