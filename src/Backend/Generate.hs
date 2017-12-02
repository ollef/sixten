{-# OPTIONS_GHC -Wno-incomplete-patterns -Wno-incomplete-record-updates #-} -- llvm-hs forces a bunch of these
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Backend.Generate where

import qualified Bound
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text.IO as Text
import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Traversable as Traversable
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Word
import IRBuilder
import qualified LLVM.AST as LLVM
import LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as LLVM
import qualified LLVM.AST.Constant as LLVM.Constant
import qualified LLVM.AST.Global as LLVM.Global
import qualified LLVM.AST.Linkage as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.AST.Type as LLVM.Type
import qualified LLVM.Pretty as LLVM
import qualified LLVM.Typed as LLVM
import System.IO

import Backend.LLVM
import qualified Backend.Target as Target
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
import VIX

type ModuleGen = ModuleBuilderT VIX
type InstrGen = IRBuilderT ModuleGen

voidT, byteT :: LLVM.Type
voidT = LLVM.void
byteT = LLVM.i8

-- TODO byte var alignment?
getAlign :: MonadVIX m => m Word32
getAlign = gets $ Target.ptrAlign . vixTarget

getIntRep :: MonadVIX m => m TypeRep
getIntRep = gets $ TypeRep.intRep . vixTarget

getPtrRep :: MonadVIX m => m TypeRep
getPtrRep = gets $ TypeRep.ptrRep . vixTarget

getTypeRep :: MonadVIX m => m TypeRep
getTypeRep = gets $ TypeRep.typeRep . vixTarget

getPiRep :: MonadVIX m => m TypeRep
getPiRep = gets $ TypeRep.piRep . vixTarget

getIntBits :: MonadVIX m => m Word32
getIntBits = gets $ Target.intBits . vixTarget

getTypeRepBits :: MonadVIX m => m Word32
getTypeRepBits = (* Target.byteBits) . fromIntegral . TypeRep.size <$> getTypeRep

integerT, typeRepT :: MonadVIX m => m LLVM.Type
integerT = LLVM.IntegerType <$> getIntBits
typeRepT = LLVM.IntegerType <$> getTypeRepBits

currentBlock :: InstrGen LLVM.Name
currentBlock
  = liftIRState
  $ gets
  $ maybe (LLVM.UnName 0) partialBlockName . builderBlock

data Direct = Void | Int | Array
  deriving (Eq, Ord, Show)

directType :: TypeRep -> Direct
directType TypeRep.UnitRep = Void
directType (TypeRep.TypeRep sz) | sz <= 8 = Int
directType _ = Array

-- TODO naming
directT :: TypeRep -> LLVM.Type
directT rep@(TypeRep.TypeRep sz) = case directType rep of
  Void -> voidT
  Int -> LLVM.IntegerType $ Target.byteBits * fromIntegral sz
  Array -> LLVM.ArrayType (fromIntegral sz) byteT

indirectT :: LLVM.Type
indirectT = LLVM.ptr byteT

hinted :: InstrGen a -> NameHint -> InstrGen a
hinted gen (NameHint (Hint Nothing)) = gen
hinted gen (NameHint (Hint (Just n))) = gen `named` fromName n

loadDirect
  :: TypeRep
  -> LLVM.Operand
  -> InstrGen LLVM.Operand
loadDirect rep o = case directType rep of
  Void -> return $ LLVM.ConstantOperand $ LLVM.Null voidT
  Int -> nonVoidCase
  Array -> nonVoidCase
  where
    t = directT rep
    nonVoidCase = do
      ptr <- bitcast o (LLVM.ptr t) `named` "direct-ptr"
      align <- getAlign
      load ptr align

storeDirect
  :: TypeRep
  -> LLVM.Operand
  -> LLVM.Operand
  -> InstrGen ()
storeDirect rep src dst = case directType rep of
  Void -> return ()
  Int -> nonVoidCase
  Array -> nonVoidCase
  where
    t = directT rep
    nonVoidCase = do
      ptr <- bitcast dst (LLVM.ptr t) `named` "direct-ptr"
      align <- getAlign
      store ptr align src
      return ()

-------------------------------------------------------------------------------
-- Vars
data Var
  = VoidVar
  | IndirectVar LLVM.Operand
  | DirectVar TypeRep LLVM.Operand
  deriving Show

loadVar :: TypeRep -> Var -> InstrGen LLVM.Operand
loadVar _ VoidVar = return $ LLVM.ConstantOperand $ LLVM.Undef LLVM.void
loadVar rep (DirectVar rep' o)
  | rep == rep' = return o
  | otherwise = error "loadVar rep mismatch"
loadVar rep (IndirectVar o) = loadDirect rep o

indirect :: Var -> InstrGen LLVM.Operand
indirect VoidVar = return $ LLVM.ConstantOperand $ LLVM.Null indirectT
indirect (DirectVar rep o) = do
  align <- getAlign
  result <- alloca (directT rep) Nothing align `named` "indirect-alloca"
  storeDirect rep o result
  bitcast result indirectT
indirect (IndirectVar o) = return o

allocaBytes :: LLVM.Operand -> InstrGen LLVM.Operand
allocaBytes o = do
  align <- getAlign
  alloca byteT (Just o) align

memcpy :: LLVM.Operand -> LLVM.Operand -> LLVM.Operand -> InstrGen ()
memcpy dst src sz = do
  bits <- getTypeRepBits
  align <- getAlign
  let args =
        [ dst
        , src
        , sz
        , LLVM.ConstantOperand $ LLVM.Int 32 $ fromIntegral align
        , LLVM.ConstantOperand $ LLVM.Int 1 0 -- isvolatile
        ]
      memcpyGlob
        = LLVM.GlobalReference
          LLVM.FunctionType
            { LLVM.resultType = LLVM.void
            , LLVM.argumentTypes = LLVM.typeOf <$> args
            , LLVM.isVarArg = False
            }
          (LLVM.Name $ "llvm.memcpy.p0i8.p0i8.i" <> shower bits)
  _ <- call (LLVM.ConstantOperand memcpyGlob) [(arg, []) | arg <- args]
  return ()

gcAlloc :: LLVM.Operand -> InstrGen LLVM.Operand
gcAlloc sz = do
  bits <- getTypeRepBits
  let gcAllocGlob
        = LLVM.GlobalReference
          LLVM.FunctionType
            { LLVM.resultType = LLVM.ptr LLVM.i8
            , LLVM.argumentTypes = [LLVM.IntegerType bits]
            , LLVM.isVarArg = False
            }
          "GC_malloc"
  byteRef <- call (LLVM.ConstantOperand gcAllocGlob) [(sz, [])]
  bitcast byteRef indirectT

varcpy :: LLVM.Operand -> Var -> LLVM.Operand -> InstrGen ()
varcpy _ VoidVar _ = return ()
varcpy dst (DirectVar rep src) _ = storeDirect rep src dst
varcpy dst (IndirectVar src) rep = memcpy dst src rep

varCall
  :: (Foldable f, Functor f)
  => Maybe Language
  -> LLVM.Operand
  -> f Var
  -> InstrGen LLVM.Operand
varCall lang fun xs = call fun (concatMap go xs) `with` \c -> c
  { LLVM.callingConvention = cc }
  where
    cc = case lang of
      Nothing -> CC.Fast
      Just Extern.C -> CC.C
    go VoidVar = []
    go (DirectVar _ x) = [(x, [])]
    go (IndirectVar x) = [(x, [])]

directed
  :: Alternative f
  => Direction
  -> Var
  -> InstrGen (f Var)
directed d v = case d of
  Direct TypeRep.UnitRep -> return empty
  Direct rep -> pure . DirectVar rep <$> loadVar rep v
  Indirect -> pure . IndirectVar <$> indirect v

-------------------------------------------------------------------------------
-- Generation
generateExpr :: Expr Var -> Expr Var -> InstrGen Var
generateExpr expr typ = case expr of
  Var v -> return v
  Global g -> generateGlobal g
  Lit l -> do
    rep <- literalRep l
    c <- literalConstant l
    return $ DirectVar rep $ LLVM.ConstantOperand c
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
      rets <- generateBranches e brs $ \branch -> do
        v <- generateExpr branch typ
        loadVar rep v `named` "branch-result"
      case rets of
        [] -> return $ DirectVar rep $ LLVM.ConstantOperand $ LLVM.Undef $ directT rep
        _ -> fmap (DirectVar rep) $ phi rets `named` "case-result"
    _ -> do
      rets <- generateBranches e brs $ \branch -> do
        v <- generateExpr branch typ
        indirect v
      case rets of
        [] -> return $ IndirectVar $ LLVM.ConstantOperand $ LLVM.Undef indirectT
        _ -> fmap IndirectVar $ phi rets `named` "case-result"
  Anno e typ' -> generateExpr e typ'

generateTypeExpr :: Expr Var -> InstrGen LLVM.Operand
generateTypeExpr expr = do
  typeRep <- getTypeRep
  repVar <- generateExpr expr $ Lit $ TypeRep typeRep
  loadVar typeRep repVar `named` "type-rep"

generateTypeSize :: Expr Var -> InstrGen LLVM.Operand
generateTypeSize (MkType rep) = do
  bits <- getTypeRepBits
  return $ LLVM.ConstantOperand $ LLVM.Int bits $ TypeRep.size rep
generateTypeSize typ = do
  rep <- generateTypeExpr typ
  generateSizeOf rep

generateSizeOf :: LLVM.Operand -> InstrGen LLVM.Operand
generateSizeOf rep = do
  typeRep <- getTypeRep
  generateIntExpr
    $ Call (Global Builtin.SizeOfName)
    $ pure $ pure $ DirectVar typeRep rep

generateIntExpr :: Expr Var -> InstrGen LLVM.Operand
generateIntExpr expr = do
  intRep <- getIntRep
  sizeVar <- generateExpr expr $ Lit $ TypeRep intRep
  loadVar intRep sizeVar `named` "size"

generateByteExpr :: Expr Var -> InstrGen LLVM.Operand
generateByteExpr expr = do
  sizeVar <- generateExpr expr $ Lit $ TypeRep TypeRep.ByteRep
  loadVar TypeRep.ByteRep sizeVar `named` "size"

unknownSize :: Name -> Expr v
unknownSize n = Global $ unqualified $ "unknownSize." <> n

generateCall
  :: Maybe Language
  -> RetDir
  -> Expr Var
  -> Vector (Direction, Expr Var)
  -> Expr Var
  -> InstrGen Var
generateCall lang retDir funExpr es typ = do
  let argDirs = fst <$> es
  fun <- generateFunOp funExpr retDir argDirs
  args <- join <$> mapM (uncurry generateDirectedExpr) es
  case retDir of
    ReturnDirect TypeRep.UnitRep -> do
      _ <- varCall lang fun args
      return VoidVar
    ReturnDirect rep -> do
      res <- varCall lang fun args `named` "call-return"
      return $ DirectVar rep res
    ReturnIndirect OutParam -> do
      sz <- generateTypeSize typ
      res <- allocaBytes sz `named` "call-return"
      _ <- varCall lang fun $ Vector.snoc args $ IndirectVar res
      return $ IndirectVar res
    ReturnIndirect Projection -> do
      res <- varCall lang fun args `named` "call-return"
      return $ IndirectVar res

storeExpr :: Expr Var -> Expr Var -> LLVM.Operand -> InstrGen ()
storeExpr expr typ out = case expr of
  Var v -> do
    sz <- generateTypeSize typ
    varcpy out v sz
  Global g -> do
    sz <- generateTypeSize typ
    v <- generateGlobal g
    varcpy out v sz
  Lit lit -> storeLit lit out
  Con qc es -> storeCon qc es out
  Call funExpr es -> do
    (retDir, argDirs) <- funSignature funExpr $ Vector.length es
    storeCall Nothing retDir funExpr (Vector.zip argDirs es) typ out
  PrimCall lang retDir funExpr es -> storeCall lang retDir funExpr es typ out
  Let _h e s -> do
    v <- generateExpr e $ unknownSize "storeLet"
    storeExpr (Bound.instantiate1 (pure v) s) typ out
  Case e brs -> void $ generateBranches e brs $ \branch -> storeExpr branch typ out
  Anno e typ' -> storeExpr e typ' out

literalRep :: Literal -> InstrGen TypeRep
literalRep Integer {} = getIntRep
literalRep Byte {} = return TypeRep.ByteRep
literalRep TypeRep {} = getTypeRep

literalConstant :: Literal -> InstrGen LLVM.Constant
literalConstant (Integer i) = do
  bits <- getIntBits
  return $ LLVM.Int bits i
literalConstant (Byte b) =
  return $ LLVM.Int 8 $ fromIntegral b
literalConstant (TypeRep r) = do
  bits <- getTypeRepBits
  return $ LLVM.Int bits $ fromIntegral $ TypeRep.size r

storeLit :: Literal -> LLVM.Operand -> InstrGen ()
storeLit lit out = do
  align <- getAlign
  c <- literalConstant lit
  castRet <- bitcast out $ LLVM.ptr $ LLVM.typeOf c
  store castRet align $ LLVM.ConstantOperand c
  return ()

storeCall
  :: Maybe Language
  -> RetDir
  -> Expr Var
  -> Vector (Direction, Expr Var)
  -> Expr Var
  -> LLVM.Operand
  -> InstrGen ()
storeCall lang retDir funExpr es typ out = do
  let argDirs = fst <$> es
  fun <- generateFunOp funExpr retDir argDirs
  args <- join <$> mapM (uncurry generateDirectedExpr) es
  case retDir of
    ReturnDirect TypeRep.UnitRep -> do
      _ <- varCall lang fun args
      return ()
    ReturnDirect rep -> do
      res <- varCall lang fun args `named` "call-return"
      storeDirect rep res out
    ReturnIndirect OutParam -> do
      _ <- varCall lang fun $ Vector.snoc args $ IndirectVar out
      return ()
    ReturnIndirect Projection -> do
      res <- varCall lang fun args `named` "call-return"
      sz <- generateTypeSize typ
      memcpy out res sz

funSignature :: Expr Var -> Int -> InstrGen (RetDir, Vector Direction)
funSignature expr arity = case expr of
  Global g -> do
    msig <- signature g
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
  -> InstrGen (f Var)
generateDirectedExpr dir expr
  = generateExpr expr (unknownSize "generateDirectedExpr") >>= directed dir

gcAllocExpr :: Expr Var -> InstrGen LLVM.Operand
gcAllocExpr (Anno expr typ) = do
  rep <- generateTypeExpr typ
  typeRep <- getTypeRep
  sz <- generateSizeOf rep
  ref <- gcAlloc sz
  let typ' = case typ of
        Lit _ -> typ
        _ -> pure $ DirectVar typeRep rep
  storeExpr expr typ' ref
  return ref
gcAllocExpr _ = error "gcAllocExpr"

productOffsets
  :: Foldable f
  => f LLVM.Operand
  -> InstrGen ([LLVM.Operand], LLVM.Operand)
productOffsets os = do
  typeRep <- getTypeRep
  typeRepBits <- getTypeRepBits
  let
    zeroTypeRep = LLVM.ConstantOperand $ LLVM.Int typeRepBits 0
    go (indices, fullRep) rep = do
      fullRep' <- generateTypeExpr
        $ Call (Global Builtin.ProductTypeRepName)
        $ Vector.fromList
          [ pure $ DirectVar typeRep fullRep
          , pure $ DirectVar typeRep rep
          ]
      index <- generateSizeOf fullRep
      return (Snoc indices index, fullRep')
  (snocResult, full) <- Foldable.foldlM go (Nil, zeroTypeRep) os
  return (Foldable.toList snocResult, full)

productOffsets'
  :: Vector LLVM.Operand
  -> InstrGen [LLVM.Operand]
productOffsets' xs = do
  typeRepBits <- getTypeRepBits
  let
    zeroTypeRep = LLVM.ConstantOperand $ LLVM.Int typeRepBits 0
    go (indices, fullRep) (i, rep) = do
      typeRep <- getTypeRep
      fullRep' <- if i == Vector.length xs - 1
        then return fullRep
        else generateTypeExpr
          $ Call (Global Builtin.ProductTypeRepName)
          $ Vector.fromList
            [ pure $ DirectVar typeRep fullRep
            , pure $ DirectVar typeRep rep
            ]
      index <- generateSizeOf fullRep
      return (Snoc indices index, fullRep')
  (snocResults, _) <- Foldable.foldlM go (Nil, zeroTypeRep) $ indexed xs
  return $ Foldable.toList snocResults

generateCon :: QConstr -> Vector (Expr Var) -> Expr Var -> InstrGen Var
generateCon Builtin.Ref es _ = do
  reps <- mapM (generateTypeExpr . typeOf) es
  (is, fullRep) <- productOffsets reps
  fullSize <- generateSizeOf fullRep
  ref <- gcAlloc fullSize
  typeRep <- getTypeRep
  Foldable.forM_ (zip (Vector.toList reps) $ zip is $ Vector.toList es) $ \(rep, (i, Anno e _)) -> do
    index <- gep ref [i] `named` "index"
    storeExpr e (pure $ DirectVar typeRep rep) index
  intType <- integerT
  refInt <- ptrtoint ref intType `named` "ref-int"
  ptrRep <- getPtrRep
  return $ DirectVar ptrRep refInt
generateCon _ _ (MkType TypeRep.UnitRep) = return VoidVar
generateCon qc es typ = do
  sz <- generateTypeSize typ
  out <- allocaBytes sz `named` "cons-cell"
  storeCon qc es out
  return $ IndirectVar out

storeCon :: QConstr -> Vector (Expr Var) -> LLVM.Operand -> InstrGen ()
storeCon Builtin.Ref es out = do
  ptrRep <- getPtrRep
  v <- generateCon Builtin.Ref es $ Lit $ TypeRep ptrRep
  i <- loadVar ptrRep v
  storeDirect ptrRep i out
storeCon qc es out = do
  intRep <- getIntRep
  typeRep <- getTypeRep
  mqcIndex <- constrIndex qc
  let es' = maybe id (Vector.cons . Sized (Lit $ TypeRep intRep) . Lit . Integer . fromIntegral) mqcIndex es
  reps <- mapM (generateTypeExpr . typeOf) es'
  is <- productOffsets' reps
  Foldable.forM_ (zip (Vector.toList reps) $ zip is $ Vector.toList es') $ \(rep, (i, Anno e _)) -> do
    index <- gep out [i] `named` "index"
    storeExpr e (pure $ DirectVar typeRep rep) index

generateFunOp :: Expr Var -> RetDir -> Vector Direction -> InstrGen LLVM.Operand
generateFunOp (Global g) retDir argDirs = do
  msig <- signature g
  let typ = case msig of
        Just sig -> signatureType sig
        Nothing -> functionType retDir argDirs
  return $ LLVM.ConstantOperand $ LLVM.GlobalReference typ $ LLVM.Name $ fromQName g
generateFunOp e retDir argDirs = do
  piRep <- getPiRep
  funVar <- generateExpr e $ Lit $ TypeRep piRep
  funInt <- loadVar piRep funVar `named` "func-int"
  funPtr <- inttoptr funInt indirectT `named` "func-ptr"
  let funType = functionType retDir argDirs
  bitcast funPtr (LLVM.ptr funType) `named` "func"

-- TODO move
signatureType
  :: Signature ReturnIndirect
  -> LLVM.Type
signatureType (ConstantSig (Direct TypeRep.UnitRep)) = LLVM.void
signatureType (ConstantSig (Direct rep)) = directT rep
signatureType (ConstantSig Indirect) = indirectT
signatureType (FunctionSig retDir args) = functionType retDir args

-- TODO move
functionType
  :: RetDir
  -> Vector Direction
  -> LLVM.Type
functionType retDir paramDirs
  = LLVM.FunctionType retType (paramTypes ++ retParam) False
  where
    (retType, retParam) = case retDir of
      ReturnDirect rep -> (directT rep, mempty)
      ReturnIndirect OutParam -> (voidT, pure indirectT)
      ReturnIndirect Projection -> (indirectT, mempty)
    paramTypes = go =<< Vector.toList paramDirs
    go (Direct rep) = case directType rep of
      Void -> []
      Int -> [directT rep]
      Array -> [directT rep]
    go Indirect = [indirectT]

generateGlobal :: QName -> InstrGen Var
generateGlobal g = do
  msig <- signature g
  ptrRep <- getPtrRep
  let typ = signatureType $ fromMaybe (ConstantSig Indirect) msig
      glob = LLVM.GlobalReference (LLVM.ptr typ) $ fromQName g
      globOperand = LLVM.ConstantOperand glob
  case msig of
    Just (ConstantSig (Direct TypeRep.UnitRep)) -> return VoidVar
    Just (ConstantSig (Direct _)) -> return
      $ IndirectVar
      $ LLVM.ConstantOperand
      $ LLVM.Constant.BitCast glob indirectT
    Just (ConstantSig Indirect) -> do
      align <- getAlign
      ptr <- load globOperand align `named` "global"
      return $ IndirectVar ptr
    Just (FunctionSig _ _) -> return
      $ DirectVar ptrRep
      $ LLVM.ConstantOperand
      $ LLVM.Constant.PtrToInt
        (LLVM.Constant.BitCast glob indirectT)
        (directT ptrRep)
    _ -> return $ IndirectVar globOperand

generateBranches
  :: Expr Var
  -> Branches QConstr () Expr Var
  -> (Expr Var -> InstrGen a)
  -> InstrGen [(a, LLVM.Name)]
generateBranches caseExpr branches brCont = do
  intRep <- getIntRep
  intBits <- getIntBits
  typeRep <- getTypeRep
  align <- getAlign
  case branches of
    ConBranches [] -> do
      void $ generateExpr caseExpr $ unknownSize "noBranches"
      unreachable
      return []
    ConBranches [ConBranch Builtin.Ref tele brScope] -> do
      genExpr <- generateExpr caseExpr $ unknownSize "caseRef"
      exprInt <- loadVar intRep genExpr `named` "case-expr-int"
      expr <- inttoptr exprInt indirectT `named` "case-expr"

      branchBlock <- freshName $ fromQConstr Builtin.Ref
      br branchBlock
      emitBlockStart branchBlock

      typeRepBits <- getTypeRepBits

      argsReps <- forTeleWithPrefixM tele $ \h () s argsReps -> do
        let args = fst <$> argsReps
            reps = snd <$> argsReps
            fullRep
              | Vector.null reps = LLVM.ConstantOperand $ LLVM.Int typeRepBits 0
              | otherwise = Vector.last reps
        index <- generateIntExpr
          $ Call (Global Builtin.SizeOfName)
          $ pure $ pure $ DirectVar typeRep fullRep
        ptr <- gep expr [index] `hinted` h
        fullRep' <- if Vector.length argsReps == teleLength tele - 1
          then return fullRep
          else do
            rep <- generateTypeExpr $ instantiateTele pure args s
            generateTypeExpr
              $ Call (Global Builtin.ProductTypeRepName)
              $ Vector.fromList
                [ pure $ DirectVar typeRep fullRep
                , pure $ DirectVar typeRep rep
                ]
        return (IndirectVar ptr, fullRep')

      let args = fst <$> argsReps

      contResult <- brCont $ instantiateTele pure args brScope
      afterBranchBlock <- currentBlock
      postBlock <- freshName "after-branches"
      br postBlock
      emitBlockStart postBlock
      return [(contResult, afterBranchBlock)]

    ConBranches cbrs -> do
      let hasTag = case cbrs of
            [_] -> False
            _ -> True

      exprGen <- generateExpr caseExpr $ unknownSize "conBranches"
      expr <- indirect exprGen `named` "case-expr"

      failBlock <- freshName "pattern-match-failed"
      branchBlocks <- forM cbrs $ \(ConBranch qc _ _) -> freshName $ fromQConstr qc

      if hasTag then do
        e0Ptr <- gep expr [LLVM.ConstantOperand $ LLVM.Int 32 0] `named` "tag-pointer"
        intType <- integerT
        e0IntPtr <- bitcast e0Ptr (LLVM.ptr intType)
        e0 <- load e0IntPtr align `named` "tag"

        constrIndices <- Traversable.forM cbrs $ \(ConBranch qc _ _) -> do
          Just qcIndex <- constrIndex qc
          return $ LLVM.Int intBits $ fromIntegral qcIndex

        switch e0 failBlock $ zip constrIndices branchBlocks
      else
        br $ head branchBlocks

      postBlock <- freshName "after-branches"

      branchResults <- Traversable.forM (zip branchBlocks cbrs) $ \(branchBlock, ConBranch _ tele brScope) -> do
        emitBlockStart branchBlock

        typeRepBits <- getTypeRepBits

        argsReps <- forTeleWithPrefixM tele $ \h () s argsReps -> do
          let args = fst <$> argsReps
              reps = snd <$> argsReps
              fullRep
                | Vector.null reps
                  = LLVM.ConstantOperand
                  $ LLVM.Int typeRepBits
                  $ if hasTag then TypeRep.size intRep else 0
                | otherwise = Vector.last reps
          index <- generateIntExpr
            $ Call (Global Builtin.SizeOfName)
            $ pure $ pure $ DirectVar typeRep fullRep
          ptr <- gep expr [index] `hinted` h
          fullRep' <- if Vector.length argsReps == teleLength tele - 1
            then return fullRep
            else do
              rep <- generateTypeExpr $ instantiateTele pure args s
              generateTypeExpr
                $ Call (Global Builtin.ProductTypeRepName)
                $ Vector.fromList
                  [ pure $ DirectVar typeRep fullRep
                  , pure $ DirectVar typeRep rep
                  ]
          return (IndirectVar ptr, fullRep')

        let args = fst <$> argsReps

        contResult <- brCont $ instantiateTele pure args brScope
        afterBranchBlock <- currentBlock
        br postBlock
        return (contResult, afterBranchBlock)

      emitBlockStart failBlock
      unreachable

      emitBlockStart postBlock
      return branchResults

    LitBranches lbrs@(LitBranch firstLit _ NonEmpty.:| _) def -> do
      let lbrs' = NonEmpty.toList lbrs

      e0 <- case firstLit of
        Integer _ -> generateIntExpr caseExpr
        Byte _ -> generateByteExpr caseExpr
        TypeRep _ -> generateTypeExpr caseExpr >>= generateSizeOf

      branchConstants <- mapM (\(LitBranch lit _) -> literalConstant lit) $ NonEmpty.toList lbrs

      defaultBlock <- freshName "default"
      branchBlocks <- forM lbrs' $ \(LitBranch l _) -> freshName $ shower l

      switch e0 defaultBlock
        $ zip branchConstants branchBlocks

      postBlock <- freshName "after-branches"

      branchResults <- Traversable.forM (zip branchBlocks lbrs') $ \(brBlock, LitBranch _ branch) -> do
        emitBlockStart brBlock
        contResult <- brCont branch
        afterBranchBlock <- currentBlock
        br postBlock
        return (contResult, afterBranchBlock)

      emitBlockStart defaultBlock
      defaultContResult <- brCont def
      afterDefaultBlock <- currentBlock
      br postBlock
      emitBlockStart postBlock
      return $ (defaultContResult, afterDefaultBlock) : branchResults

generateConstant :: Visibility -> QName -> Constant Expr Var -> ModuleGen (InstrGen ())
generateConstant visibility name (Constant e) = do
  msig <- signature name
  align <- getAlign
  intBits <- getIntBits
  typeRepBits <- getTypeRepBits
  let gname = fromQName name
      linkage = case visibility of
        Private -> LLVM.Private
        Public -> LLVM.External
      directLit l rep = do
        emitDefn $ LLVM.GlobalDefinition LLVM.globalVariableDefaults
          { LLVM.Global.name = gname
          , LLVM.Global.linkage = linkage
          , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
          , LLVM.Global.isConstant = True
          , LLVM.Global.type' = directT rep
          , LLVM.Global.initializer = Just l
          , LLVM.Global.alignment = align
          }
        return $ return ()
  case msig of
    Just (ConstantSig dir) ->
      case (e, dir) of
        (Anno (Lit lit) _, Direct rep) -> case lit of
          Byte b -> directLit (LLVM.Int 8 $ fromIntegral b) rep
          Integer i -> directLit (LLVM.Int intBits i) rep
          TypeRep t -> directLit (LLVM.Int typeRepBits $ TypeRep.size t) rep
        _ -> do
          let typ = case dir of
                Indirect -> indirectT
                Direct TypeRep.UnitRep -> indirectT
                Direct rep -> directT rep
          let glob = LLVM.GlobalReference (LLVM.ptr typ) gname
          emitDefn $ LLVM.GlobalDefinition LLVM.globalVariableDefaults
            { LLVM.Global.name = gname
            , LLVM.Global.linkage = linkage
            , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
            , LLVM.Global.initializer = Just $ LLVM.Null typ
            -- , LLVM.Global.isConstant = True
            , LLVM.Global.type' = typ
            , LLVM.Global.alignment = align
            }
          initBody <- execIRBuilderT emptyIRBuilder $ case dir of
            Direct TypeRep.UnitRep -> do
              _ <- generateExpr e $ Lit $ TypeRep TypeRep.UnitRep
              retVoid
              return ()
            Direct rep -> do
              storeExpr e (Lit $ TypeRep rep)
                $ LLVM.ConstantOperand
                $ LLVM.Constant.BitCast glob indirectT
              retVoid
            Indirect -> do
              ptr <- gcAllocExpr e
              store (LLVM.ConstantOperand glob) align ptr
              retVoid
              return ()
          let initName = LLVM.Name $ fromQName name <> "-init"
              voidFunType = LLVM.FunctionType
                { LLVM.resultType = LLVM.void
                , LLVM.argumentTypes = []
                , LLVM.isVarArg = False
                }
              initOperand = LLVM.ConstantOperand $ LLVM.GlobalReference voidFunType initName
          emitDefn $ LLVM.GlobalDefinition LLVM.functionDefaults
            { LLVM.Global.name = initName
            , LLVM.Global.linkage = LLVM.Private
            , LLVM.Global.returnType = LLVM.void
            , LLVM.Global.basicBlocks = initBody
            }
          return
            $ void
            $ call initOperand [] `with` \c -> c
              { LLVM.callingConvention = CC.Fast }
    _ -> error "generateConstant"

generateFunction :: Visibility -> QName -> Function Expr Var -> ModuleGen ()
generateFunction visibility name (Function args funScope) = do
  Just (FunctionSig retDir argDirs) <- signature name
  ((retType, params), basicBlocks) <- runIRBuilderT emptyIRBuilder $ do
    paramVars <- iforMTele args $ \i h _ _sz -> do
      let d = argDirs Vector.! i
      case d of
        Direct TypeRep.UnitRep -> return ([], VoidVar)
        Direct rep -> do
          n <- IRBuilder.fresh `hinted` h
          return
            ( [LLVM.Parameter (directT rep) n []]
            , DirectVar rep $ LLVM.LocalReference (directT rep) n
            )
        Indirect -> do
          n <- IRBuilder.fresh `hinted` h
          return
            ( [LLVM.Parameter indirectT n []]
            , IndirectVar $ LLVM.LocalReference indirectT n
            )

    let funExpr = instantiateTele pure (snd <$> paramVars) funScope
        params = concat $ fst <$> paramVars

    case retDir of
      ReturnDirect TypeRep.UnitRep -> do
        _ <- generateExpr funExpr $ Lit $ TypeRep TypeRep.UnitRep
        retVoid
        return
          (voidT
          , params
          )
      ReturnDirect rep -> do
        res <- generateExpr funExpr $ Lit $ TypeRep rep
        dres <- loadVar rep res
        ret dres
        return
          ( directT rep
          , params
          )
      ReturnIndirect OutParam -> do
        outParamName <- IRBuilder.fresh `hinted` "return"
        let outParam = LLVM.LocalReference indirectT outParamName
        storeExpr funExpr (unknownSize "generateFunction OutParam") outParam
        retVoid
        return
          ( voidT
          , params <> pure (LLVM.Parameter indirectT outParamName [])
          )
      ReturnIndirect Projection -> do
        res <- generateExpr funExpr $ unknownSize "generateFunction Projection"
        resPtr <- indirect res `named` "function-result"
        ret resPtr
        return
          ( indirectT
          , params
          )
  let linkage = case visibility of
        Private -> LLVM.Private
        Public -> LLVM.External
  emitDefn $ LLVM.GlobalDefinition LLVM.functionDefaults
    { LLVM.Global.name = fromQName name
    , LLVM.Global.callingConvention = CC.Fast
    , LLVM.Global.basicBlocks = basicBlocks
    , LLVM.Global.parameters = (params, False)
    , LLVM.Global.returnType = retType
    , LLVM.Global.linkage = linkage
    }

generateDefinition :: QName -> Definition Expr Var -> ModuleGen (InstrGen ())
generateDefinition name def = case def of
  ConstantDef v c ->
    generateConstant v name c
  FunctionDef v _ f -> do
    generateFunction v name f
    return $ return ()
  AliasDef -> return $ return ()

generateDeclaration :: Declaration -> ModuleGen ()
generateDeclaration decl
  = declareFun (declRetDir decl) (fromName $ declName decl) (declArgDirs decl)

declareFun
  :: RetDir
  -> LLVM.Name
  -> Vector Direction
  -> ModuleGen ()
declareFun retDir name argDirs = do
  let LLVM.FunctionType retType argTypes _varArg = functionType retDir argDirs
  _ <- extern name argTypes retType
  return ()

declareConstant
  :: Direction
  -> LLVM.Name
  -> ModuleGen ()
declareConstant dir name = do
  -- TODO make function out of this
  let typ = case dir of
        Indirect -> indirectT
        Direct TypeRep.UnitRep -> indirectT
        Direct rep -> directT rep
  align <- getAlign
  emitDefn $ LLVM.GlobalDefinition LLVM.globalVariableDefaults
    { LLVM.Global.name = name
    , LLVM.Global.linkage = LLVM.External
    , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
    , LLVM.Global.isConstant = True
    , LLVM.Global.type' = typ
    , LLVM.Global.initializer = Nothing
    , LLVM.Global.alignment = align
    }

data GeneratedSubmodule = GeneratedSubmodule
  { declarations :: HashMap QName [LLVM.Definition]
  , definitions :: [LLVM.Definition]
  , initCode :: InstrGen ()
  , externs :: [(Language, Text)]
  }

generateSubmodule
  :: QName
  -> Extracted.Submodule (Definition Expr Var)
  -> VIX GeneratedSubmodule
generateSubmodule name modul = do
  let def = submoduleContents modul

  let globalDeps
        = HashSet.toList
        $ HashSet.filter ((/= qnameModule name) . qnameModule)
        -- These may be emitted by the code generator, so are implicit
        -- dependencies of most code
        $ HashSet.insert Builtin.SizeOfName
        $ HashSet.insert Builtin.ProductTypeRepName
        $ boundGlobals def

  decls <- forM globalDeps $ \g -> do
    msig <- signature g
    decls <- execModuleBuilderT emptyModuleBuilder $ case msig of
      Just (FunctionSig retDir argDirs) -> declareFun retDir (fromQName g) argDirs
      Just (ConstantSig dir) -> declareConstant dir (fromQName g)
      Just (AliasSig _) -> return ()
      Nothing -> return ()
    return (g, decls)

  (i, defs) <- runModuleBuilderT emptyModuleBuilder $ do
    mapM_ generateDeclaration $ submoduleExternDecls modul
    generateDefinition name def

  return GeneratedSubmodule
    { declarations = HashMap.fromList decls
    , definitions = defs
    , initCode = i
    , externs = submoduleExterns $ modul
    }

generateModule
  :: ModuleName
  -> [Import]
  -> [GeneratedSubmodule]
  -> ModuleGen ()
generateModule mname imports gens = do
  let decls = concat $ HashMap.elems $ mconcat $ declarations <$> gens
  let importedModules = HashSet.toList $ HashSet.fromList $ importModule <$> imports
  forM_ decls emitDefn
  forM_ gens $ \gen -> forM (definitions gen) emitDefn

  let initName mn = LLVM.Name $ fromModuleName mn <> "-init"
      initOperand mn = LLVM.ConstantOperand $ LLVM.GlobalReference voidFun $ initName mn
      thisInitName = initName mname
      thisInitedName = LLVM.Name $ fromModuleName mname <> "-inited"
      thisInitedOperand
        = LLVM.ConstantOperand $ LLVM.GlobalReference (LLVM.ptr LLVM.i1) thisInitedName
      gcInitOperand = LLVM.ConstantOperand $ LLVM.GlobalReference voidFun "GC_init"
      voidFun = LLVM.FunctionType
        { LLVM.resultType = LLVM.void
        , LLVM.argumentTypes = []
        , LLVM.isVarArg = False
        }

  forM_ importedModules $ \i ->
    declareFun (ReturnDirect TypeRep.UnitRep) (initName i) mempty

  emitDefn $ LLVM.GlobalDefinition LLVM.globalVariableDefaults
    { LLVM.Global.name = thisInitedName
    , LLVM.Global.linkage = LLVM.Private
    , LLVM.Global.unnamedAddr = Just LLVM.GlobalAddr
    , LLVM.Global.type' = LLVM.i1
    , LLVM.Global.initializer = Just $ LLVM.Int 1 0
    }

  initBasicBlocks <- execIRBuilderT emptyIRBuilder $ do
    let align = 1
    isInited <- load thisInitedOperand align `named` "is-inited"
    notInited <- freshName "not-inited"
    inited <- freshName "inited"
    switch isInited notInited [(LLVM.Int 1 1, inited)]
    emitBlockStart inited;
      retVoid
    emitBlockStart notInited; do
      _ <- store thisInitedOperand align $ LLVM.ConstantOperand $ LLVM.Int 1 1
      _ <- call gcInitOperand []
      forM_ importedModules $ \i ->
        call (initOperand i) [] `with` \c -> c
          { LLVM.callingConvention = CC.Fast }
      forM_ gens initCode
      retVoid
    return ()

  emitDefn $ LLVM.GlobalDefinition LLVM.functionDefaults
    { LLVM.Global.name = thisInitName
    , LLVM.Global.callingConvention = CC.Fast
    , LLVM.Global.basicBlocks = initBasicBlocks
    , LLVM.Global.parameters = ([], False)
    , LLVM.Global.returnType = voidT
    , LLVM.Global.linkage = LLVM.External
    }

  let globalCtorType = LLVM.StructureType
        { LLVM.Type.isPacked = False
        , LLVM.elementTypes = [LLVM.i32, LLVM.ptr voidFun, LLVM.ptr LLVM.i8]
        }

  emitDefn $ LLVM.GlobalDefinition LLVM.globalVariableDefaults
    { LLVM.Global.name = "llvm.global_ctors"
    , LLVM.Global.linkage = LLVM.Appending
    , LLVM.Global.type' = LLVM.ArrayType 1 globalCtorType
    , LLVM.Global.initializer
      = Just
      $ LLVM.Array globalCtorType
      [ LLVM.Struct
        { LLVM.Constant.structName = Nothing
        , LLVM.Constant.isPacked = False
        , LLVM.Constant.memberValues =
          [ LLVM.Int 32 610
          , LLVM.GlobalReference (LLVM.ptr voidFun) thisInitName
          , LLVM.Null $ LLVM.ptr LLVM.i8
          ]
        }
      ]
    }

  when (mname == "Main") $ void $
    function "main" [] LLVM.i32 $ \_ ->
      ret $ LLVM.ConstantOperand $ LLVM.Int 32 0

writeLlvmModule
  :: ModuleName
  -> [Import]
  -> [GeneratedSubmodule]
  -> Handle
  -> VIX ()
writeLlvmModule mname imports gens handle = do
  forwardDecls <- liftIO $ Text.readFile =<< getDataFileName "rts/forwarddecls.ll"
  liftIO $ Text.hPutStrLn handle forwardDecls
  modul <- buildModuleT (fromModuleName mname) $ generateModule mname imports gens
  liftIO $ Lazy.hPutStrLn handle $ LLVM.ppllvm modul
