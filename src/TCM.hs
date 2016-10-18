{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, Rank2Types, TypeFamilies, OverloadedStrings #-}
module TCM where

import Control.Monad.Except
import Control.Monad.State(MonadState, evalStateT, StateT, gets, modify)
import Control.Monad.ST
import Control.Monad.ST.Class
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import Data.HashMap.Lazy(HashMap)
import Data.List as List
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text.Lazy as Lazy
import qualified Data.Text.Lazy.IO as Lazy
import qualified Data.Vector as Vector
import Data.Void
import System.IO

import qualified Builtin
import Syntax
import Syntax.Abstract
import qualified Syntax.Converted as Converted
import Util

newtype Level = Level Int
  deriving (Eq, Num, Ord, Show)

instance Pretty Level where
  pretty (Level i) = pretty i

data State = State
  { tcContext :: Program ExprP Void
  , tcConstrs :: HashMap Constr (Set (Name, TypeP Void))
  , tcErasableContext :: Program ExprE Void
  , tcConvertedSignatures :: HashMap Name (Converted.Signature Converted.Expr Unit Void)
  , tcIndent :: !Int -- This has no place here, but is useful for debugging
  , tcFresh :: !Int
  , tcLevel :: !Level
  , tcLogHandle :: !Handle
  }

emptyState :: Handle -> State
emptyState handle = State
  { tcContext = mempty
  , tcConstrs = mempty
  , tcErasableContext = mempty
  , tcConvertedSignatures = mempty
  , tcIndent = 0
  , tcFresh = 0
  , tcLevel = Level 1
  , tcLogHandle = handle
  }

newtype TCM a = TCM (ExceptT String (StateT State IO) a)
  deriving (Functor, Applicative, Monad, MonadFix, MonadError String, MonadState State, MonadIO)

instance MonadST TCM where
  type World TCM = RealWorld
  liftST = TCM . liftST

unTCM
  :: TCM a
  -> ExceptT String (StateT State IO) a
unTCM (TCM x) = x

runTCM
  :: TCM a
  -> Handle
  -> IO (Either String a)
runTCM tcm handle
  = evalStateT (runExceptT $ unTCM tcm)
  $ emptyState handle

fresh :: TCM Int
fresh = do
  i <- gets tcFresh
  modify $ \s -> s {tcFresh = i + 1}
  return i

level :: TCM Level
level = gets tcLevel

enterLevel :: TCM a -> TCM a
enterLevel x = do
  l <- level
  modify $ \s -> s {tcLevel = l + 1}
  r <- x
  modify $ \s -> s {tcLevel = l}
  return r

-------------------------------------------------------------------------------
-- Debugging
log :: Lazy.Text -> TCM ()
log l = do
  h <- gets tcLogHandle
  liftIO $ Lazy.hPutStrLn h l

modifyIndent :: (Int -> Int) -> TCM ()
modifyIndent f = modify $ \s -> s {tcIndent = f $ tcIndent s}

trp :: Pretty a => String -> a -> TCM ()
trp s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> showWide (pretty x)

trs :: Show a => String -> a -> TCM ()
trs s x = do
  i <- gets tcIndent
  TCM.log $ mconcat (replicate i "| ") <> "--" <> fromString s <> ": " <> fromString (show x)

-------------------------------------------------------------------------------
-- Context class
class Context e where
  definition :: Name -> TCM (Definition e v, e v)
  typeOfSize :: Integer -> e v
  qconstructor :: QConstr -> TCM (e v)

-------------------------------------------------------------------------------
-- Working with abstract syntax
addContext :: Program ExprP Void -> TCM ()
addContext prog = modify $ \s -> s
  { tcContext = prog <> tcContext s
  , tcConstrs = HM.unionWith (<>) cs $ tcConstrs s
  } where
    cs = HM.fromList $ do
      (n, (DataDefinition d, defType)) <- HM.toList prog
      ConstrDef c t <- quantifiedConstrTypes d defType $ const Implicit
      return (c, Set.fromList [(n, t)])

addConvertedSignatures
  :: HashMap Name (Converted.Signature Converted.Expr b c)
  -> TCM ()
addConvertedSignatures p = modify $ \s -> s { tcConvertedSignatures = p' <> tcConvertedSignatures s }
  where
    p' = fmap (const $ error "addConvertedSignatures")
       . Converted.hoistSignature (const Unit) <$> p

instance Context (Expr Plicitness) where
  definition name = do
    mres <- gets $ HM.lookup name . tcContext
    maybe (throwError $ "Not in scope: " ++ show name)
          (return . bimap vacuous vacuous)
          mres

  qconstructor qc@(QConstr n c) = do
    (def, typ) <- definition n
    case def of
      DataDefinition dataDef -> do
        let qcs = quantifiedConstrTypes dataDef typ $ const Implicit
        case filter ((== c) . constrName) qcs of
          [] -> throwError $ "Not in scope: constructor " ++ show qc
          [cdef] -> return $ constrType cdef
          _ -> throwError $ "Ambiguous constructor: " ++ show qc
      Definition _ -> throwError $ "Not a data type: " ++ show n

  typeOfSize = Builtin.TypeP . Lit

constructor
  :: Ord v
  => Either Constr QConstr
  -> TCM (Set (Name, TypeP v))
constructor (Right qc@(QConstr n _)) = Set.singleton . (,) n <$> qconstructor qc
constructor (Left c) 
  = gets
  $ maybe mempty (Set.map $ second vacuous)
  . HM.lookup c
  . tcConstrs

-------------------------------------------------------------------------------
-- Erasable
addErasableContext :: Program ExprE Void -> TCM ()
addErasableContext prog = modify $ \s -> s
  { tcErasableContext = prog <> tcErasableContext s
  }

instance Context (Expr Erasability) where
  definition name = do
    mres <- gets $ HM.lookup name . tcErasableContext
    maybe (throwError $ "Not in scope: " ++ show name)
          (return . bimap vacuous vacuous)
          mres

  qconstructor qc@(QConstr n c) = do
    (def, typ) <- definition n
    case def of
      DataDefinition dataDef -> do
        let qcs = quantifiedConstrTypes dataDef typ $ const Erased
        case filter ((== c) . constrName) qcs of
          [] -> throwError $ "Not in scope: constructor " ++ show qc
          [cdef] -> return $ constrType cdef
          _ -> throwError $ "Ambiguous constructor: " ++ show qc
      Definition _ -> throwError $ "Not a data type: " ++ show n

  typeOfSize = Builtin.TypeE . Lit

-------------------------------------------------------------------------------
-- Converted
convertedSignature
  :: Name
  -> TCM (Converted.Signature Converted.Expr Unit Void)
convertedSignature name = do
  mres <- gets $ HM.lookup name . tcConvertedSignatures
  maybe (throwError $ "Not in scope: converted " ++ show name)
        return
        mres

-------------------------------------------------------------------------------
-- General constructor queries
qconstructorIndex :: TCM (QConstr -> Maybe Int)
qconstructorIndex = do
  cxt <- gets tcContext
  return $ \(QConstr n c) -> do
    (DataDefinition (DataDef constrDefs), _) <- HM.lookup n cxt
    case constrDefs of
      [] -> Nothing
      [_] -> Nothing
      _ -> findIndex ((== c) . constrName) constrDefs

constrArity
  :: QConstr
  -> TCM Int
constrArity
  = fmap (teleLength . fst . pisView)
  . (qconstructor :: QConstr -> TCM (ExprP Void))

constrIndex
  :: QConstr
  -> TCM Int
constrIndex qc@(QConstr n c) = do
  (DataDefinition (DataDef cs), _) <- (definition n :: TCM (Definition ExprP Void, ExprP Void))
  case List.findIndex ((== c) . constrName) cs of
    Just i -> return i
    Nothing -> throwError $ "Can't find index for " ++ show qc

retainedConstrArity
  :: QConstr
  -> TCM Int
retainedConstrArity
  = fmap ( Vector.length
         . Vector.filter (\(_, er, _) -> er == Retained)
         . unTelescope
         . fst
         . pisView)
  . (qconstructor :: QConstr -> TCM (ExprE Void))
