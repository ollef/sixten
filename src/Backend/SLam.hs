{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, MonadComprehensions, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances, ViewPatterns #-}
module Backend.SLam where

import Bound.Scope hiding (instantiate1)
import Control.Monad.Except
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Inference.MetaVar
import Inference.Monad
import Inference.Normalise
import Inference.TypeOf
import MonadContext
import MonadFresh
import Syntax
import qualified Syntax.Core as Core
import Syntax.Sized.Anno
import qualified Syntax.Sized.SLambda as SLambda
import TypedFreeVar
import Util
import VIX

newtype SLam a = SLam { runSlam :: VIX a }
  deriving (Functor, Applicative, Monad, MonadFix, MonadIO, MonadVIX, MonadFresh, MonadError Error)

-- | Dummy instance, since we don't use the context
instance MonadContext FreeV SLam where
  localVars = return mempty
  inUpdatedContext _ m = m

slamAnno :: CoreM -> SLam (Anno SLambda.Expr FreeV)
slamAnno e = Anno <$> slam e <*> (slam =<< whnfExpandingTypeReps =<< typeOf e)

slam :: CoreM -> SLam (SLambda.Expr FreeV)
slam expr = do
  logMeta 20 "slam expr" expr
  res <- indentLog $ case expr of
    Core.Var v -> return $ SLambda.Var v
    Core.Meta _ _ -> error "slam Meta"
    Core.Global g -> return $ SLambda.Global g
    Core.Lit l -> return $ SLambda.Lit l
    Core.Pi {} -> do
      t <- whnfExpandingTypeReps $ Core.Global Builtin.PiTypeName
      slam t
    Core.Lam h p t s -> do
      t' <- whnfExpandingTypeReps t
      v <- freeVar h p t'
      e <- slamAnno $ instantiate1 (pure v) s
      rep <- slam t'
      return $ SLambda.lam v rep e
    (Core.appsView -> (Core.Con qc@(QConstr typeName _), es)) -> do
      (DataDefinition (DataDef params _) _, _) <- definition typeName
      n <- constrArity qc
      case compare (length es) n of
        GT -> internalError $ "slam: too many args for constructor:" PP.<+> shower qc
        EQ -> do
          let numParams = teleLength params
              es' = drop numParams es
          SLambda.Con qc <$> mapM slamAnno (Vector.fromList $ snd <$> es')
        LT -> do
          conType <- qconstructor qc
          let Just appliedConType = Core.typeApps conType es
              tele = Core.piTelescope appliedConType
          slam
            $ quantify Core.Lam tele
            $ Scope
            $ Core.apps (Core.Con qc)
            $ Vector.fromList (fmap (pure . pure) <$> es)
            <> iforTele tele (\i _ a _ -> (a, pure $ B $ TeleVar i))
    Core.Con _qc -> internalError "slam impossible"
    Core.App e1 _ e2 -> SLambda.App <$> slam e1 <*> slamAnno e2
    Core.Case e brs _retType -> SLambda.Case <$> slamAnno e <*> slamBranches brs
    Core.Let ds scope -> do
      vs <- forMLet ds $ \h _ t -> freeVar h Explicit t
      ds' <- forMLet ds $ \_ s t -> do
        e <- slam $ instantiateLet pure vs s
        t' <- slam t
        return $ Anno e t'
      body <- slam $ instantiateLet pure vs scope
      return $ SLambda.letRec (Vector.zip vs ds') body
    Core.ExternCode c retType -> do
        retType' <- slam =<< whnfExpandingTypeReps retType
        c' <- slamExtern c
        return $ SLambda.ExternCode c' retType'
  logPretty 20 "slam res" $ pretty <$> res
  return res

slamBranches
  :: Branches Plicitness (Core.Expr MetaVar) FreeV
  -> SLam (Branches () SLambda.Expr FreeV)
slamBranches (ConBranches cbrs) = do
  cbrs' <- indentLog $ forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> freeVar h p $ instantiateTele pure vs s
    reps <- forM vs $ \v -> do
      t' <- whnfExpandingTypeReps $ varType v
      slam t'

    brExpr <- slam $ instantiateTele pure vs brScope
    return $ typedConBranchTyped c (Vector.zip vs reps) brExpr
  logPretty 20 "slamBranches res" $ pretty <$> ConBranches cbrs'
  return $ ConBranches cbrs'
slamBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> slam e | LitBranch l e <- lbrs]
    <*> slam d

slamExtern
  :: Extern CoreM
  -> SLam (Extern (Anno SLambda.Expr FreeV))
slamExtern (Extern lang parts)
  = fmap (Extern lang) $ forM parts $ \part -> case part of
    ExternPart str -> return $ ExternPart str
    ExprMacroPart e -> ExprMacroPart <$> slamAnno e
    TypeMacroPart t -> TypeMacroPart <$> (slamAnno =<< whnfExpandingTypeReps t)
    TargetMacroPart m -> return $ TargetMacroPart m

slamDef
  :: Definition (Core.Expr MetaVar) FreeV
  -> SLam (Anno SLambda.Expr FreeV)
slamDef (ConstantDefinition _ _ e) = slamAnno e
slamDef (DataDefinition _ e) = slamAnno e
