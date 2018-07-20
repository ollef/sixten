{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Backend.Generate.Types where

import Control.Applicative
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Word
import qualified LLVM.AST as LLVM
import LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.AST.Typed as LLVM
import LLVM.IRBuilder

import Backend.Generate.LLVM
import qualified Backend.Target as Target
import Syntax.Direction
import Syntax.Extern(Language)
import qualified Syntax.Extern as Extern
import TypeRep(TypeRep)
import qualified TypeRep
import Util
import VIX

loadStoreAlign :: Word32
loadStoreAlign = 1

-------------------------------------------------------------------------------
-- Types
integerType :: MonadVIX m => m LLVM.Type
integerType = LLVM.IntegerType <$> getIntBits

directType :: TypeRep -> LLVM.Type
directType TypeRep.UnitRep = LLVM.void
directType (TypeRep.TypeRep sz)
  | sz <= 8 = LLVM.IntegerType $ Target.byteBits * fromIntegral sz
  | otherwise = LLVM.ArrayType (fromIntegral sz) LLVM.i8

indirectType :: LLVM.Type
indirectType = LLVM.ptr LLVM.i8

zeroInitializer :: LLVM.Type -> LLVM.Constant
zeroInitializer (LLVM.IntegerType width) = LLVM.Int width 0
zeroInitializer typ = LLVM.Null typ

loadDirect
  :: MonadIRBuilder m
  => TypeRep
  -> LLVM.Operand
  -> m LLVM.Operand
loadDirect TypeRep.UnitRep _ = return $ LLVM.ConstantOperand $ LLVM.Null LLVM.void
loadDirect rep o = do
  ptr <- bitcast o (LLVM.ptr $ directType rep) `named` "direct-ptr"
  load ptr loadStoreAlign

storeDirect
  :: MonadIRBuilder m
  => TypeRep
  -> LLVM.Operand
  -> LLVM.Operand
  -> m ()
storeDirect TypeRep.UnitRep _ _ = return ()
storeDirect rep src dst = do
  ptr <- bitcast dst (LLVM.ptr $ directType rep) `named` "direct-ptr"
  store ptr loadStoreAlign src
  return ()

-------------------------------------------------------------------------------
-- Vars
data Var
  = VoidVar
  | IndirectVar LLVM.Operand
  | DirectVar TypeRep LLVM.Operand
  deriving Show

loadVar :: MonadIRBuilder m => TypeRep -> Var -> m LLVM.Operand
loadVar _ VoidVar = return $ LLVM.ConstantOperand $ LLVM.Undef LLVM.void
loadVar rep (DirectVar rep' o)
  | rep == rep' = return o
  | otherwise = error "loadVar rep mismatch"
loadVar rep (IndirectVar o) = loadDirect rep o

indirect :: (MonadIRBuilder m, MonadVIX m) => Var -> m LLVM.Operand
indirect VoidVar = return $ LLVM.ConstantOperand $ LLVM.Null indirectType
indirect (DirectVar rep o) = do
  align <- getPtrAlign
  result <- alloca (directType rep) Nothing align `named` "indirect-alloca"
  storeDirect rep o result
  bitcast result indirectType
indirect (IndirectVar o) = return o

varcpy :: (MonadIRBuilder m, MonadVIX m) => LLVM.Operand -> Var -> LLVM.Operand -> m ()
varcpy _ VoidVar _ = return ()
varcpy dst (DirectVar rep src) _ = storeDirect rep src dst
varcpy dst (IndirectVar src) rep = memcpy dst src rep

varCall
  :: (Foldable f, Functor f, MonadIRBuilder m)
  => Maybe Language
  -> LLVM.Operand
  -> f Var
  -> m LLVM.Operand
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
  :: (Alternative f, MonadIRBuilder m, MonadVIX m)
  => Direction
  -> Var
  -> m (f Var)
directed d v = case d of
  Direct TypeRep.UnitRep -> return empty
  Direct rep -> pure . DirectVar rep <$> loadVar rep v
  Indirect -> pure . IndirectVar <$> indirect v

signatureType
  :: Signature ReturnIndirect
  -> LLVM.Type
signatureType (ConstantSig (Direct TypeRep.UnitRep)) = LLVM.void
signatureType (ConstantSig (Direct rep)) = directType rep
signatureType (ConstantSig Indirect) = indirectType
signatureType (FunctionSig _ retDir args) = functionType retDir args
signatureType (AliasSig _) = error "signatureType alias"

functionType
  :: RetDir
  -> Vector Direction
  -> LLVM.Type
functionType retDir paramDirs
  = LLVM.FunctionType retType (paramTypes ++ retParam) False
  where
    (retType, retParam) = case retDir of
      ReturnDirect rep -> (directType rep, mempty)
      ReturnIndirect OutParam -> (LLVM.void, pure indirectType)
      ReturnIndirect Projection -> (indirectType, mempty)
    paramTypes = go =<< Vector.toList paramDirs
    go (Direct TypeRep.UnitRep) = []
    go (Direct rep) = [directType rep]
    go Indirect = [indirectType]

-------------------------------------------------------------------------------
-- Memory operations
memcpy :: (MonadIRBuilder m, MonadVIX m) => LLVM.Operand -> LLVM.Operand -> LLVM.Operand -> m ()
memcpy dst src sz = do
  bits <- getTypeRepBits
  let args =
        [ dst
        , src
        , sz
        , LLVM.ConstantOperand $ LLVM.Int 32 $ fromIntegral loadStoreAlign
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

gcAlloc :: (MonadIRBuilder m, MonadVIX m) => LLVM.Operand -> m LLVM.Operand
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
  bitcast byteRef indirectType

allocaBytes :: (MonadIRBuilder m, MonadVIX m) => LLVM.Operand -> m LLVM.Operand
allocaBytes o = do
  align <- getPtrAlign
  alloca LLVM.i8 (Just o) align
