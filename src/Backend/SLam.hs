{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving, MonadComprehensions, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances, ViewPatterns #-}
module Backend.SLam where

import Bound.Scope hiding (instantiate1)
import Control.Monad.Except
import Control.Monad.Fail
import Data.Bifunctor
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Data.Void
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

annotateType :: (meta -> ()) -> Core.Expr meta FreeV -> SLam (Core.Expr () FreeV)
annotateType meta t = do
  t' <- whnf $ first meta t
  annotateExpr id t'

annotate' :: Core.Expr () FreeV -> Core.Expr () FreeV -> (Core.Expr () FreeV, Core.Expr () FreeV)
annotate' e t = (Core.Meta () $ toVector [(Explicit, t), (Explicit, e)], t)

annotateExpr'
  :: Core.Expr Void FreeV
  -> SLam (Core.Expr () FreeV, Core.Expr () FreeV)
annotateExpr' expr = uncurry annotate' <$> case expr of
  Core.Var v -> return (Core.Var v, varType v)
  Core.Meta m _ -> absurd m
  Core.Global g -> do
    (_, typ) <- definition g
    typ' <- whnf typ
    return (Core.Global g, typ')
  Core.Lit l -> return (Core.Lit l, TypeOf.typeOfLiteral l)
  Core.Pi h p t s -> do
    (t', _) <- annotateExpr' t
    t'' <- whnf t'
    v <- freeVar h p t''
    (e, _) <- annotateExpr' $ instantiate1 (pure v) s
    typ <- whnf Builtin.Type
    return (Core.pi_ v e, typ)
  Core.Lam h p t s -> do
    (t', _) <- annotateExpr' t
    t'' <- whnf t'
    v <- freeVar h p t''
    (body, bodyType) <- annotateExpr' $ instantiate1 (pure v) s
    return (Core.lam v body, Core.pi_ v bodyType)
  Core.Con qc -> do
    typ <- qconstructor qc
    typ' <- whnf typ
    return (Core.Con qc, typ')
  (Core.appsView -> (e, es@(_:_))) -> do
    (e', eType) <- annotateExpr' e
    es' <- mapM (mapM (fmap fst . annotateExpr')) es
    resType <- appType eType es'
    return (Core.apps e' es', resType)
  Core.App {} -> error "annotateExpr impossible"
  Core.Case e brs retType -> do
    (e', _) <- annotateExpr' e
    brs' <- annotateBranches' brs
    (retType', _) <- annotateExpr' retType
    retType'' <- whnf retType'
    return (Core.Case e' brs' retType'', retType'')
  Core.Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      (t', _) <- annotateExpr' t
      t'' <- whnf t'
      freeVar h Explicit t''
    es' <- forMLet ds $ \_ s _ -> do
      (e, _) <- annotateExpr' $ instantiateLet pure vs s
      return e
    (body, bodyType) <- annotateExpr' $ instantiateLet pure vs scope
    let ves = Vector.zip vs es'
    resType <- whnf $ Core.let_ ves bodyType
    return (Core.let_ ves body, resType)
  Core.ExternCode c retType -> do
    c' <- mapM (fmap fst . annotateExpr') c
    (retType', _) <- annotateExpr' retType
    retType'' <- whnf retType'
    return (Core.ExternCode c' retType'', retType'')
  where
    appType typ es = do
      typ' <- whnf typ
      appType' typ' es
    appType' typ [] = return typ
    appType' (Core.Pi _ p _ s) ((p', e):es) | p == p' = appType (instantiate1 e s) es
    appType' _ _ = error "SLam appType"

annotateBranches'
  :: Branches Plicitness (Core.Expr Void) FreeV
  -> SLam (Branches Plicitness (Core.Expr ()) FreeV)
annotateBranches' (ConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      (t, _) <- annotateExpr' $ instantiateTele pure vs s
      t' <- whnf t
      freeVar h p t'
    (brExpr, _) <- annotateExpr' $ instantiateTele pure vs brScope
    return $ conBranchTyped c vs brExpr
  return $ ConBranches cbrs'
annotateBranches' (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l . fst <$> annotateExpr' e | LitBranch l e <- lbrs]
    <*> fmap fst (annotateExpr' d)

annotateExpr :: (meta -> ()) -> Core.Expr meta FreeV -> SLam (Core.Expr () FreeV)
annotateExpr meta expr = annotate =<< case expr of
  Core.Var v -> return $ Core.Var v
  Core.Meta m es -> Core.Meta (meta m) <$> mapM (mapM $ annotateExpr meta) es
  Core.Global g -> return $ Core.Global g
  Core.Lit l -> return $ Core.Lit l
  Core.Pi h p t s -> do
    t' <- annotateType meta t
    v <- freeVar h p t'
    e <- annotateExpr meta $ instantiate1 (pure v) s
    return $ Core.pi_ v e
  Core.Lam h p t s -> do
    t' <- annotateType meta t
    v <- freeVar h p t'
    e <- annotateExpr meta $ instantiate1 (pure v) s
    return $ Core.lam v e
  Core.Con qc -> return $ Core.Con qc
  (Core.appsView -> (e, es@(_:_))) -> do
    e' <- annotateExpr meta e
    es' <- mapM (mapM $ annotateExpr meta) es
    return $ Core.apps e' es'
  Core.App {} -> error "annotateExpr impossible"
  Core.Case e brs retType -> do
    e' <- annotateExpr meta e
    brs' <- annotateBranches meta brs
    retType' <- annotateType meta retType
    return $ Core.Case e' brs' retType'
  Core.Let ds scope -> do
    vs <- forMLet ds $ \h _ t -> do
      t' <- annotateType meta t
      freeVar h Explicit t'
    es' <- forMLet ds $ \_ s _ ->
      annotateExpr meta $ instantiateLet pure vs s
    body <- annotateExpr meta $ instantiateLet pure vs scope
    return $ Core.let_ (Vector.zip vs es') body
  Core.ExternCode c retType -> do
    c' <- mapM (annotateExpr meta) c
    retType' <- annotateType meta retType
    return $ Core.ExternCode c' retType'

annotateBranches
  :: (meta -> ())
  -> Branches Plicitness (Core.Expr meta) FreeV
  -> SLam (Branches Plicitness (Core.Expr ()) FreeV)
annotateBranches meta (ConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      t <- annotateType meta $ instantiateTele pure vs s
      freeVar h p t
    brExpr <- annotateExpr meta $ instantiateTele pure vs brScope
    return $ conBranchTyped c vs brExpr
  return $ ConBranches cbrs'
annotateBranches meta (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> annotateExpr meta e | LitBranch l e <- lbrs]
    <*> annotateExpr meta d

-- | Dummy instance, since we don't use the context
instance MonadContext FreeV SLam where
  localVars = return mempty
  inUpdatedContext _ m = m

slamAnno :: Core.Expr () FreeV -> SLam (Anno SLambda.Expr FreeV)
slamAnno e = Anno <$> slam e <*> (slam =<< typeOf e)

unMeta :: Core.Expr () v -> Core.Expr () v
unMeta (Core.Meta () es) = snd $ es Vector.! 1
unMeta e = e

slam :: Core.Expr () FreeV -> SLam (SLambda.Expr FreeV)
slam expr = do
  logPretty 20 "slam expr" $ pretty <$> expr
  res <- indentLog $ case expr of
    Core.Var v -> return $ SLambda.Var v
    Core.Meta () es -> slam $ snd $ es Vector.! 1
    Core.Global g -> return $ SLambda.Global g
    Core.Lit l -> return $ SLambda.Lit l
    Core.Pi {} -> slam $ Core.Global Builtin.PiTypeName
    Core.Lam h p t s -> do
      v <- freeVar h p t
      e <- slamAnno $ instantiate1 (pure v) s
      rep <- slam t
      return $ SLambda.lam v rep e
    (Core.appsView -> (unMeta -> Core.Con qc@(QConstr typeName _), es)) -> do
      (DataDefinition (DataDef params _) _, _) <- definition typeName
      n <- constrArity qc
      case compare (length es) n of
        GT -> internalError $ "slam: too many args for constructor:" PP.<+> shower qc
        EQ -> do
          let numParams = teleLength params
              es' = drop numParams es
          SLambda.Con qc <$> mapM slamAnno (Vector.fromList $ snd <$> es')
        LT -> do
          VIX.log $ "eta expanding " <> shower (pretty qc) <> " " <> shower (length es) <> " " <> shower n
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
  VIX.log "Annotating"
  (e', _) <- annotateExpr' e
  VIX.log "Annotation done, slamming"
  res <- slamAnno e'
  VIX.log "Slam done"
  return res
slamDef (DataDefinition _ e) = do
  VIX.log "Annotating"
  (e', _) <- annotateExpr' e
  VIX.log "Annotation done, slamming"
  res <- slamAnno e'
  VIX.log "Slam done"
  return res
