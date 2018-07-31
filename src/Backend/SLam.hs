{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MonadComprehensions, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances, ViewPatterns #-}
module Backend.SLam where

import Bound.Scope hiding (instantiate1)
import Control.Monad.Except
import Control.Monad.Fail
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import qualified Inference.Normalise as Normalise
import qualified Inference.TypeOf as TypeOf
import MonadContext
import MonadFresh
import Syntax
import qualified Syntax.Core as Core
import Syntax.Sized.Anno
import qualified Syntax.Sized.SLambda as SLambda
import TypedFreeVar
import Util
import VIX
import Data.Void

type FreeV = FreeVar Plicitness (Core.Expr ())

newtype SLam a = SLam { runSlam :: VIX a }
  deriving (Functor, Applicative, Monad, MonadFail, MonadFix, MonadIO, MonadVIX, MonadFresh, MonadError Error)

whnf :: Core.Expr () FreeV -> SLam (Core.Expr () FreeV)
whnf e = Normalise.whnf' normaliseArgs e mempty

normalise :: Core.Expr () FreeV -> SLam (Core.Expr () FreeV)
normalise e = Normalise.normalise' normaliseArgs e mempty

normaliseArgs :: Normalise.Args meta SLam
normaliseArgs = Normalise.Args
  { Normalise.expandTypeReps = True
  , Normalise.handleMetaVar = \_ -> return
    $ Just $ close id
    $ Core.Lam mempty Explicit Builtin.Type
    $ Scope
    $ Core.Lam mempty Explicit (pure $ B ())
    $ Scope $ pure $ B ()
  }

typeOf :: Core.Expr () FreeV -> SLam (Core.Expr () FreeV)
typeOf = TypeOf.typeOf' TypeOf.Args
  { TypeOf.typeOfMeta = \_ -> close id
    $ Core.Pi mempty Explicit Builtin.Type
    $ Scope
    $ Core.Pi mempty Explicit (pure $ B ())
    $ Scope $ pure $ F $ pure $ B ()
  , TypeOf.normaliseArgs = normaliseArgs
  }

annotate :: Core.Expr () FreeV -> SLam (Core.Expr () FreeV)
annotate e = do
  t <- typeOf e
  t' <- whnf t
  return $ Core.Meta () $ toVector [(Explicit, t'), (Explicit, e)]

annotateType :: Core.Expr Void FreeV -> SLam (Core.Expr () FreeV)
annotateType = annotateExpr >=> whnf

annotateExpr :: Core.Expr Void FreeV -> SLam (Core.Expr () FreeV)
annotateExpr expr = annotate =<< case expr of
  Core.Var v -> return $ Core.Var v
  Core.Meta m _ -> absurd m
  Core.Global g -> return $ Core.Global g
  Core.Lit l -> return $ Core.Lit l
  Core.Pi h p t s -> do
    t' <- annotateType t
    v <- freeVar h p t'
    e <- annotateExpr $ instantiate1 (pure v) s
    return $ Core.pi_ v e
  Core.Lam h p t s -> do
    t' <- annotateType t
    v <- freeVar h p t'
    e <- annotateExpr $ instantiate1 (pure v) s
    return $ Core.lam v e
  Core.Con qc -> return $ Core.Con qc
  Core.App e1 p e2 -> annotate =<< do
    e1' <- annotateExpr e1
    e2' <- annotateExpr e2
    return $ Core.App e1' p e2'
  Core.Case e brs retType -> do
    e' <- annotateExpr e
    brs' <- annotateBranches brs
    retType' <- annotateType retType
    return $ Core.Case e' brs' retType'
  Core.Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      t' <- annotateType t
      freeVar h Explicit t'
    es' <- forMLet ds $ \_ s _ ->
      annotateExpr $ instantiateLet pure vs s
    body <- annotateExpr $ instantiateLet pure vs scope
    return $ Core.let_ (Vector.zip vs es') body
  Core.ExternCode c retType -> do
    c' <- mapM annotateExpr c
    retType' <- annotateType retType
    return $ Core.ExternCode c' retType'

annotateBranches
  :: Branches Plicitness (Core.Expr Void) FreeV
  -> SLam (Branches Plicitness (Core.Expr ()) FreeV)
annotateBranches (ConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      t <- annotateType $ instantiateTele pure vs s
      freeVar h p t
    brExpr <- annotateExpr $ instantiateTele pure vs brScope
    return $ conBranchTyped c vs brExpr
  return $ ConBranches cbrs'
annotateBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> annotateExpr e | LitBranch l e <- lbrs]
    <*> annotateExpr d

-- | Dummy instance, since we don't use the context
instance MonadContext FreeV SLam where
  localVars = return mempty
  inUpdatedContext _ m = m

slamAnno :: Core.Expr () FreeV -> SLam (Anno SLambda.Expr FreeV)
slamAnno e = Anno <$> slam e <*> (slam =<< typeOf e)

slam :: Core.Expr () FreeV -> SLam (SLambda.Expr FreeV)
slam expr = do
  logPretty 20 "slam expr" $ pretty <$> expr
  res <- indentLog $ case expr of
    Core.Var v -> return $ SLambda.Var v
    Core.Meta () es -> slam $ snd $ es Vector.! 1
    Core.Global g -> return $ SLambda.Global g
    Core.Lit l -> return $ SLambda.Lit l
    Core.Pi {} -> do
      t <- whnf $ Core.Global Builtin.PiTypeName
      slam t
    Core.Lam h p t s -> do
      v <- freeVar h p t
      e <- slamAnno $ instantiate1 (pure v) s
      rep <- slam t
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
      retType' <- slam retType
      c' <- slamExtern c
      return $ SLambda.ExternCode c' retType'
  logPretty 20 "slam res" $ pretty <$> res
  return res

slamBranches
  :: Branches Plicitness (Core.Expr ()) FreeV
  -> SLam (Branches () SLambda.Expr FreeV)
slamBranches (ConBranches cbrs) = do
  cbrs' <- indentLog $ forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      let t = instantiateTele pure vs s
      freeVar h p t
    reps <- forM vs $ \v ->
      slam $ varType v

    brExpr <- slam $ instantiateTele pure vs brScope
    return $ typedConBranchTyped c (Vector.zip vs reps) brExpr
  logPretty 20 "slamBranches res" $ pretty <$> ConBranches cbrs'
  return $ ConBranches cbrs'
slamBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> slam e | LitBranch l e <- lbrs]
    <*> slam d

slamExtern
  :: Extern (Core.Expr () FreeV)
  -> SLam (Extern (Anno SLambda.Expr FreeV))
slamExtern (Extern lang parts)
  = fmap (Extern lang) $ forM parts $ \part -> case part of
    ExternPart str -> return $ ExternPart str
    ExprMacroPart e -> ExprMacroPart <$> slamAnno e
    TypeMacroPart t -> TypeMacroPart <$> slamAnno t
    TargetMacroPart m -> return $ TargetMacroPart m

slamDef
  :: Definition (Core.Expr Void) FreeV
  -> SLam (Anno SLambda.Expr FreeV)
slamDef (ConstantDefinition _ e) = do
  e' <- annotateExpr e
  slamAnno e'
slamDef (DataDefinition _ e) = do
  e' <- annotateExpr e
  slamAnno e'
