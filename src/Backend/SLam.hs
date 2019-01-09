{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, LambdaCase, MonadComprehensions, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances, ViewPatterns #-}
module Backend.SLam where

import Protolude

import Bound.Scope hiding (instantiate1)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import Effect.Log as Log
import qualified Elaboration.Normalise as Normalise
import qualified Elaboration.TypeOf as TypeOf
import Syntax
import qualified Syntax.Core as Core
import Syntax.Sized.Anno
import qualified Syntax.Sized.SLambda as SLambda
import TypedFreeVar
import Util
import VIX

type FreeV = FreeVar (Core.Expr Void)

newtype SLam a = SLam { runSlam :: VIX a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFresh, MonadReport, MonadLog, MonadFetch Query)

whnf :: Core.Expr Void FreeV -> SLam (Core.Expr Void FreeV)
whnf e = Normalise.whnf' Normalise.voidArgs
  { Normalise._expandTypeReps = True
  } e mempty

typeOf :: Core.Expr Void FreeV -> SLam (Core.Expr Void FreeV)
typeOf = TypeOf.typeOf' TypeOf.voidArgs

-- | Dummy instance, since we don't use the context
instance MonadContext FreeV SLam where
  getLocalVars = return mempty
  inUpdatedContext _ m = m

slamAnno :: Core.Expr Void FreeV -> SLam (Anno SLambda.Expr FreeV)
slamAnno e = Anno <$> slam e <*> (slam =<< whnf =<< typeOf e)

typeArity :: Core.Type a b -> Int
typeArity = teleLength . fst . Core.pisView

slam :: Core.Expr Void FreeV -> SLam (SLambda.Expr FreeV)
slam expr = do
  logPretty "slam" "slam expr" $ pretty <$> expr
  res <- Log.indent $ case expr of
    Core.Var v -> return $ SLambda.Var v
    Core.Meta m _ -> absurd m
    Core.Global g -> return $ SLambda.Global g
    Core.Lit l -> return $ SLambda.Lit l
    Core.Pi {} -> do
      t <- whnf $ Core.Global $ gname Builtin.PiTypeName
      slam t
    Core.Lam h p t s -> do
      t' <- whnf t
      v <- freeVar h p t'
      e <- slamAnno $ instantiate1 (pure v) s
      rep <- slam t'
      return $ SLambda.lam v rep e
    (Core.appsView -> (Core.unSourceLoc -> Core.Con qc@(QConstr typeName _), es)) -> do
      def <- fetchDefinition $ gname typeName
      case def of
        ConstantDefinition {} -> panic "slam qc ConstantDefintion"
        DataDefinition (DataDef params _) _ -> do
          conType <- fetchQConstructor qc
          let n = typeArity conType
          case compare (length es) n of
            GT -> panic $ "slam: too many args for constructor: " <> shower qc
            EQ -> do
              let numParams = teleLength params
                  es' = drop numParams es
              SLambda.Con qc <$> mapM slamAnno (Vector.fromList $ snd <$> es')
            LT -> do
              let Just appliedConType = Core.typeApps conType es
                  tele = Core.piTelescope appliedConType
              slam
                $ quantify Core.Lam tele
                $ Scope
                $ Core.apps (Core.Con qc)
                $ Vector.fromList (fmap (pure . pure) <$> es)
                <> iforTele tele (\i _ a _ -> (a, pure $ B $ TeleVar i))
    Core.Con _qc -> panic "slam impossible"
    Core.App e1 _ e2 -> SLambda.App <$> slam e1 <*> slamAnno e2
    Core.Case e brs _retType -> SLambda.Case <$> slamAnno e <*> slamBranches brs
    Core.Let ds scope -> do
      vs <- forMLet ds $ \h _ _ t -> freeVar h Explicit t
      ds' <- forMLet ds $ \_ _ s t -> do
        e <- slam $ instantiateLet pure vs s
        t' <- slam t
        return $ Anno e t'
      body <- slam $ instantiateLet pure vs scope
      return $ SLambda.letRec (Vector.zip vs ds') body
    Core.ExternCode c retType -> do
      retType' <- slam =<< whnf retType
      c' <- slamExtern c
      return $ SLambda.ExternCode c' retType'
    Core.SourceLoc _ e -> slam e
  logPretty "slam" "slam res" $ pretty <$> res
  return res

slamBranches
  :: Branches (Core.Expr Void) FreeV
  -> SLam (Branches SLambda.Expr FreeV)
slamBranches (ConBranches cbrs) = do
  cbrs' <- Log.indent $ forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> freeVar h p $ instantiateTele pure vs s
    reps <- forM vs $ \v -> do
      t' <- whnf $ varType v
      slam t'

    brExpr <- slam $ instantiateTele pure vs brScope
    return $ typedConBranchTyped c (Vector.zip vs reps) brExpr
  logPretty "slam" "slamBranches res" $ pretty <$> ConBranches cbrs'
  return $ ConBranches cbrs'
slamBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> slam e | LitBranch l e <- lbrs]
    <*> slam d

slamExtern
  :: Extern (Core.Expr Void FreeV)
  -> SLam (Extern (Anno SLambda.Expr FreeV))
slamExtern (Extern lang parts)
  = fmap (Extern lang) $ forM parts $ \case
    ExternPart str -> return $ ExternPart str
    ExprMacroPart e -> ExprMacroPart <$> slamAnno e
    TypeMacroPart t -> TypeMacroPart <$> (slamAnno =<< whnf t)
    TargetMacroPart m -> return $ TargetMacroPart m

slamDef
  :: Definition (Core.Expr Void) FreeV
  -> SLam (Anno SLambda.Expr FreeV)
slamDef (ConstantDefinition _ e) = slamAnno e
slamDef (DataDefinition _ e) = slamAnno e
