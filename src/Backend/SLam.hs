{-# LANGUAGE MonadComprehensions, OverloadedStrings, ViewPatterns #-}
module Backend.SLam where

import Bound.Scope hiding (instantiate1)
import Control.Monad.Except
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Inference.Meta
import Inference.Normalise
import Inference.TypeOf
import Syntax
import qualified Syntax.Abstract as Abstract
import Syntax.Sized.Anno
import qualified Syntax.Sized.SLambda as SLambda
import Util
import VIX

slamAnno :: AbstractM -> VIX (Anno SLambda.Expr MetaA)
slamAnno e = Anno <$> slam e <*> (slam =<< whnfExpandingTypeReps =<< typeOf e)

slam :: AbstractM -> VIX LambdaM
slam expr = do
  logMeta 20 "slam expr" expr
  res <- indentLog $ case expr of
    Abstract.Var v@MetaVar { metaRef = Exists r } -> do
      sol <- solution r
      case sol of
        Left _ -> return $ SLambda.Var v
        Right expr' -> slam expr'
    Abstract.Var v@MetaVar { metaRef = Forall } -> return $ SLambda.Var v
    Abstract.Var v@MetaVar { metaRef = LetRef {} } -> return $ SLambda.Var v
    Abstract.Global g -> return $ SLambda.Global g
    Abstract.Lit l -> return $ SLambda.Lit l
    Abstract.Pi {} -> do
      t <- whnfExpandingTypeReps $ Abstract.Global Builtin.PiTypeName
      slam t
    Abstract.Lam h p t s -> do
      t' <- whnfExpandingTypeReps t
      v <- forall h p t'
      e <- slamAnno $ instantiate1 (pure v) s
      rep <- slam t'
      return $ SLambda.Lam h rep $ abstract1Anno v e
    (Abstract.appsView -> (Abstract.Con qc@(QConstr typeName _), es)) -> do
      (_, typeType) <- definition typeName
      n <- constrArity qc
      case compare (length es) n of
        GT -> internalError $ "slam: too many args for constructor:" PP.<+> shower qc
        EQ -> do
          let numParams = teleLength $ Abstract.telescope typeType
              es' = drop numParams es
          SLambda.Con qc <$> mapM slamAnno (Vector.fromList $ snd <$> es')
        LT -> do
          conType <- qconstructor qc
          let Just appliedConType = Abstract.typeApps conType $ snd <$> es
              tele = Abstract.telescope appliedConType
          slam
            $ Abstract.lams tele
            $ Scope
            $ Abstract.apps (Abstract.Con qc)
            $ Vector.fromList (fmap (pure . pure) <$> es)
            <> iforTele tele (\i _ a _ -> (a, pure $ B $ TeleVar i))
    Abstract.Con _qc -> internalError "slam impossible"
    Abstract.App e1 _ e2 -> SLambda.App <$> slam e1 <*> slamAnno e2
    Abstract.Case e brs _retType -> SLambda.Case <$> slamAnno e <*> slamBranches brs
    Abstract.Let ds scope -> do
      vs <- forMLet ds $ \h _ t -> forall h Explicit t
      let abstr = letAbstraction vs
      ds' <- fmap LetRec $ forMLet ds $ \h s t -> do
        e <- slam $ instantiateLet pure vs s
        t' <- slam t
        return $ LetBinding h (abstract abstr e) t'
      body <- slam $ instantiateLet pure vs scope
      let scope' = abstract abstr body
      return $ SLambda.Let ds' scope'
    Abstract.ExternCode c retType -> do
        retType' <- slam =<< whnfExpandingTypeReps retType
        c' <- slamExtern c
        return $ SLambda.ExternCode c' retType'
  logMeta 20 "slam res" res
  return res

slamBranches
  :: Branches Plicitness Abstract.Expr MetaA
  -> VIX (Branches () SLambda.Expr MetaA)
slamBranches (ConBranches cbrs) = do
  logMeta 20 "slamBranches brs" $ ConBranches cbrs
  cbrs' <- indentLog $ forM cbrs $ \(ConBranch c tele brScope) -> do
    tele' <- forTeleWithPrefixM tele $ \h p s tele' -> do
      let vs = fst <$> tele'
          abstr = teleAbstraction vs
          t = instantiateTele pure vs s
      trep <- slam =<< whnfExpandingTypeReps t
      v <- forall h p t
      return (v, TeleArg h p $ abstract abstr trep)
    let vs = fst <$> tele'
        abstr = teleAbstraction vs
        tele'' = Telescope
               $ fmap (\(TeleArg h _ t) -> TeleArg h () t)
               $ snd <$> tele'
    brScope' <- slam $ instantiateTele pure vs brScope
    return $ ConBranch c tele'' $ abstract abstr brScope'
  logMeta 20 "slamBranches res" $ ConBranches cbrs'
  return $ ConBranches cbrs'
slamBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> slam e | LitBranch l e <- lbrs]
    <*> slam d

slamExtern
  :: Extern (Abstract.Expr MetaA)
  -> VIX (Extern (Anno SLambda.Expr MetaA))
slamExtern (Extern lang parts)
  = fmap (Extern lang) $ forM parts $ \part -> case part of
    ExternPart str -> return $ ExternPart str
    ExprMacroPart e -> ExprMacroPart <$> slamAnno e
    TypeMacroPart t -> TypeMacroPart <$> (slamAnno =<< whnfExpandingTypeReps t)
    TargetMacroPart m -> return $ TargetMacroPart m

slamDef
  :: Definition Abstract.Expr MetaA
  -> VIX (Anno SLambda.Expr MetaA)
slamDef (Definition _ _ e) = slamAnno e
slamDef (DataDefinition _ e) = slamAnno e
