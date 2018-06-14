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
import qualified Syntax.Abstract as Abstract
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

slamAnno :: AbstractM -> SLam (Anno SLambda.Expr FreeV)
slamAnno e = Anno <$> slam e <*> (slam =<< whnfExpandingTypeReps =<< typeOf e)

slam :: AbstractM -> SLam (SLambda.Expr FreeV)
slam expr = do
  logMeta 20 "slam expr" expr
  res <- indentLog $ case expr of
    Abstract.Var v -> return $ SLambda.Var v
    Abstract.Meta _ _ -> error "slam Meta"
    Abstract.Global g -> return $ SLambda.Global g
    Abstract.Lit l -> return $ SLambda.Lit l
    Abstract.Pi {} -> do
      t <- whnfExpandingTypeReps $ Abstract.Global Builtin.PiTypeName
      slam t
    Abstract.Lam h p t s -> do
      t' <- whnfExpandingTypeReps t
      v <- freeVar h p t'
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
          let Just appliedConType = Abstract.typeApps conType es
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
      vs <- forMLet ds $ \h _ t -> freeVar h Explicit t
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
  logPretty 20 "slam res" $ pretty <$> res
  return res

slamBranches
  :: Branches Plicitness (Abstract.Expr MetaVar) FreeV
  -> SLam (Branches () SLambda.Expr FreeV)
slamBranches (ConBranches cbrs) = do
  -- TODO
  -- logPretty 20 "slamBranches brs" $ pretty <$> ConBranches cbrs
  cbrs' <- indentLog $ forM cbrs $ \(ConBranch c tele brScope) -> do
    tele' <- forTeleWithPrefixM tele $ \h p s tele' -> do
      let vs = fst <$> tele'
          abstr = teleAbstraction vs
          t = instantiateTele pure vs s
      trep <- slam =<< whnfExpandingTypeReps t
      v <- freeVar h p t
      return (v, TeleArg h p $ abstract abstr trep)
    let vs = fst <$> tele'
        abstr = teleAbstraction vs
        tele'' = Telescope
               $ fmap (\(TeleArg h _ t) -> TeleArg h () t)
               $ snd <$> tele'
    brScope' <- slam $ instantiateTele pure vs brScope
    return $ ConBranch c tele'' $ abstract abstr brScope'
  logPretty 20 "slamBranches res" $ pretty <$> ConBranches cbrs'
  return $ ConBranches cbrs'
slamBranches (LitBranches lbrs d)
  = LitBranches
    <$> sequence [LitBranch l <$> slam e | LitBranch l e <- lbrs]
    <*> slam d

slamExtern
  :: Extern AbstractM
  -> SLam (Extern (Anno SLambda.Expr FreeV))
slamExtern (Extern lang parts)
  = fmap (Extern lang) $ forM parts $ \part -> case part of
    ExternPart str -> return $ ExternPart str
    ExprMacroPart e -> ExprMacroPart <$> slamAnno e
    TypeMacroPart t -> TypeMacroPart <$> (slamAnno =<< whnfExpandingTypeReps t)
    TargetMacroPart m -> return $ TargetMacroPart m

slamDef
  :: Definition (Abstract.Expr MetaVar) FreeV
  -> SLam (Anno SLambda.Expr FreeV)
slamDef (Definition _ _ e) = slamAnno e
slamDef (DataDefinition _ e) = slamAnno e
