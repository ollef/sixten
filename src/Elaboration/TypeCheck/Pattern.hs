{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Elaboration.TypeCheck.Pattern where

import Protolude

import Data.HashSet(HashSet)
import Data.IORef
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Elaboration.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import Effect.Log as Log
import Elaboration.Constructor
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.Subtype
import Elaboration.TypeCheck.Literal
import Syntax
import qualified Syntax.Core as Core
import Syntax.Core.Pattern as Core
import qualified Syntax.Pre.Scoped as Pre
import TypedFreeVar
import Util

data ExpectedPat
  = InferPat (IORef CoreM)
  | CheckPat CoreM

data BindingType = WildcardBinding | VarBinding
  deriving (Eq, Show)

instance Pretty BindingType where pretty = shower

type PatVars = Vector (BindingType, FreeV)
type BoundPatVars = Vector FreeV

boundPatVars :: PatVars -> BoundPatVars
boundPatVars = fmap snd . Vector.filter ((== VarBinding) . fst)

withPatVars :: MonadContext FreeV m => PatVars -> m a -> m a
withPatVars vs = withVars $ snd <$> vs

checkPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) ()
  -> BoundPatVars
  -> Polytype
  -> Elaborate (Core.Pat CoreM FreeV, CoreM, PatVars)
checkPat p pat vs expectedType = tcPat p pat vs $ CheckPat expectedType

inferPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) ()
  -> BoundPatVars
  -> Elaborate (Core.Pat CoreM FreeV, CoreM, PatVars, Polytype)
inferPat p pat vs = do
  ref <- liftIO $ newIORef $ panic "inferPat: empty result"
  (pat', patExpr, vs') <- tcPat p pat vs $ InferPat ref
  t <- liftIO $ readIORef ref
  return (pat', patExpr, vs', t)

tcPats
  :: Vector (Plicitness, Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) ())
  -> BoundPatVars
  -> Telescope Plicitness (Core.Expr MetaVar) FreeV
  -> Elaborate (Vector (Core.Pat CoreM FreeV, CoreM, CoreM), PatVars)
tcPats pats vs tele = do
  unless (Vector.length pats == teleLength tele)
    $ panic "tcPats length mismatch"

  results <- iforTeleWithPrefixM tele $ \i _ _ s results -> do
    let argExprs = snd3 . fst <$> results
        expectedType = instantiateTele identity argExprs s
        (p, pat) = pats Vector.! i
        -- TODO could be more efficient
        varPrefix = snd =<< results
        vs' = vs <> boundPatVars varPrefix
    logShow "tc.pat" "tcPats vars" (varId <$> vs')
    (pat', patExpr, vs'') <- withPatVars varPrefix $ checkPat p pat vs' expectedType
    return ((pat', patExpr, expectedType), vs'')

  return (fst <$> results, snd =<< results)

tcPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) ()
  -> BoundPatVars
  -> ExpectedPat
  -> Elaborate (Core.Pat CoreM FreeV, CoreM, PatVars)
tcPat p pat vs expected = do
  whenLoggingCategory "tc.pat" $ do
    let shownPat = first (pretty . fmap pretty . instantiatePattern pure vs) pat
    logPretty "tc.pat" "tcPat" shownPat
  logPretty "tc.pat" "tcPat vs" vs
  (pat', patExpr, vs') <- Log.indent $ tcPat' p pat vs expected
  logPretty "tc.pat" "tcPat vs res" vs'
  logMeta "tc.pat" "tcPat patExpr" $ zonk patExpr
  return (pat', patExpr, vs')

tcPat'
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeV) ()
  -> BoundPatVars
  -> ExpectedPat
  -> Elaborate (Core.Pat CoreM FreeV, CoreM, PatVars)
tcPat' p pat vs expected = case pat of
  Pre.VarPat h () -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType h
        liftIO $ writeIORef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall h p expectedType
    return (Core.VarPat h v, pure v, pure (VarBinding, v))
  Pre.WildcardPat -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType "_"
        liftIO $ writeIORef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall "_" p expectedType
    return (Core.VarPat "_" v, pure v, pure (WildcardBinding, v))
  Pre.LitPat lit -> do
    let (expr, typ) = inferLit lit
        pat' = litPat lit
    (pat'', expr') <- instPatExpected expected typ pat' expr
    return (pat'', expr', mempty)
  Pre.ConPat cons pats -> do
    qc@(QConstr typeName _) <- resolveConstr cons $ case expected of
      CheckPat expectedType -> Just expectedType
      InferPat _ -> Nothing
    def <- fetchDefinition $ gname typeName
    case def of
      ConstantDefinition {} -> panic "tcPat' ConstantDefinition"
      DataDefinition (DataDef paramsTele _) _ -> do
        conType <- fetchQConstructor qc

        let numParams = teleLength paramsTele
            (tele, retScope) = Core.pisView conType
            argPlics = Vector.drop numParams $ teleAnnotations tele

        pats' <- Vector.fromList <$> exactlyEqualisePats (Vector.toList argPlics) (Vector.toList pats)

        paramVars <- forTeleWithPrefixM paramsTele $ \h p' s paramVars ->
          exists h p' $ instantiateTele identity paramVars s

        let argTele = instantiatePrefix paramVars tele

        (pats'', vs') <- tcPats pats' vs argTele

        let argExprs = snd3 <$> pats''
            argTypes = thd3 <$> pats''
            pats''' = Vector.zip3 argPlics (fst3 <$> pats'') argTypes
            params = Vector.zip (teleAnnotations paramsTele) paramVars
            iparams = first implicitise <$> params
            patExpr = Core.apps (Core.Con qc) $ iparams <> Vector.zip argPlics argExprs

            retType = instantiateTele identity (paramVars <|> argExprs) retScope

        (pat', patExpr') <- instPatExpected expected retType (Core.ConPat qc params pats''') patExpr

        return (pat', patExpr', vs')
  Pre.AnnoPat pat' s -> do
    let patType = instantiatePattern pure vs s
    patType' <- checkPoly patType Builtin.Type
    (pat'', patExpr, vs') <- checkPat p pat' vs patType'
    (pat''', patExpr') <- instPatExpected expected patType' pat'' patExpr
    return (pat''', patExpr', vs')
  Pre.ViewPat _ _ -> panic "tcPat ViewPat undefined TODO"
  Pre.PatLoc loc pat' -> located loc $ do
    (pat'', patExpr, vs') <- tcPat' p pat' vs expected
    return (pat'', Core.SourceLoc loc patExpr, vs')

instPatExpected
  :: ExpectedPat
  -> Polytype -- ^ patType
  -> Core.Pat CoreM FreeV -- ^ pat
  -> CoreM -- ^ :: patType
  -> Elaborate (Core.Pat CoreM FreeV, CoreM) -- ^ (pat :: expectedType, :: expectedType)
instPatExpected (CheckPat expectedType) patType pat patExpr = do
  f <- subtype expectedType patType
  viewPat expectedType pat patExpr f
instPatExpected (InferPat ref) patType pat patExpr = do
  liftIO $ writeIORef ref patType
  return (pat, patExpr)

viewPat
  :: CoreM -- ^ expectedType
  -> Core.Pat CoreM FreeV -- ^ pat
  -> CoreM -- ^ :: patType
  -> (CoreM -> CoreM) -- ^ expectedType -> patType
  -> Elaborate (Core.Pat CoreM FreeV, CoreM) -- ^ (expectedType, :: expectedType)
viewPat expectedType pat patExpr f = do
  x <- forall mempty Explicit expectedType
  let fx = f $ pure x
  if fx == pure x then
    return (pat, patExpr)
  else do
    let fExpr = Core.lam x fx
    return (Core.ViewPat fExpr pat, pure x)

patToTerm
  :: Core.Pat CoreM FreeV
  -> Elaborate (Maybe CoreM)
patToTerm pat = case pat of
  Core.VarPat _ v -> return $ Just $ Core.Var v
  Core.ConPat qc params pats -> do
    mterms <- mapM (\(p, pat', _typ') -> fmap ((,) p) <$> patToTerm pat') pats
    case sequence mterms of
      Nothing -> return Nothing
      Just terms -> return $ Just $
        Core.apps (Core.Con qc) $ params <> terms
  Core.LitPat l -> return $ Just $ Core.Lit l
  Core.ViewPat{} -> return Nothing

--------------------------------------------------------------------------------
-- "Equalisation" -- making the patterns match a list of parameter plicitnesses
-- by adding implicits
exactlyEqualisePats
  :: Pretty c
  => [Plicitness]
  -> [(Plicitness, Pre.Pat c e ())]
  -> Elaborate [(Plicitness, Pre.Pat c e ())]
exactlyEqualisePats [] [] = return []
exactlyEqualisePats [] ((p, pat):_) = do
  reportLocated
    $ PP.vcat
      [ "Too many patterns for type"
      , "Found the pattern:" PP.<+> red (pretty $ prettyAnnotation p (prettyM $ first (const ()) pat)) <> "."
      , bold "Expected:" PP.<+> "no more patterns."
      ]
  return []
exactlyEqualisePats (Constraint:ps) ((Constraint, pat):pats)
  = (:) (Implicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Constraint:ps) pats
  = (:) (Constraint, Pre.WildcardPat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Implicit:ps) pats
  = (:) (Implicit, Pre.WildcardPat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:ps) ((Constraint, pat):pats) = do
  reportExpectedExplicit pat
  exactlyEqualisePats (Explicit:ps) pats
exactlyEqualisePats (Explicit:ps) ((Implicit, pat):pats) = do
  reportExpectedExplicit pat
  exactlyEqualisePats (Explicit:ps) pats
exactlyEqualisePats (Explicit:ps) [] = do
  reportLocated
    $ PP.vcat
      [ "Not enough patterns for type"
      , "Found: no patterns."
      , bold "Expected:" PP.<+> "an explicit pattern."
      ]
  exactlyEqualisePats (Explicit:ps) [(Explicit, Pre.WildcardPat)]

equalisePats
  :: (Pretty c)
  => [Plicitness]
  -> [(Plicitness, Pre.Pat c e ())]
  -> Elaborate [(Plicitness, Pre.Pat c e ())]
equalisePats _ [] = return []
equalisePats [] pats = return pats
equalisePats (Constraint:ps) ((Constraint, pat):pats)
  = (:) (Constraint, pat) <$> equalisePats ps pats
equalisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> equalisePats ps pats
equalisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> equalisePats ps pats
equalisePats (Constraint:ps) pats
  = (:) (Constraint, Pre.WildcardPat) <$> equalisePats ps pats
equalisePats (Implicit:ps) pats
  = (:) (Implicit, Pre.WildcardPat) <$> equalisePats ps pats
equalisePats (Explicit:ps) ((Implicit, pat):pats) = do
  reportExpectedExplicit pat
  equalisePats (Explicit:ps) pats
equalisePats (Explicit:ps) ((Constraint, pat):pats) = do
  reportExpectedExplicit pat
  equalisePats (Explicit:ps) pats

reportExpectedExplicit :: (Pretty v, Pretty c) => Pre.Pat c e v -> Elaborate ()
reportExpectedExplicit pat
  = reportLocated
  $ PP.vcat
    [ "Explicit/implicit mismatch"
    , "Found the implicit pattern:" PP.<+> red (pretty $ prettyAnnotation Implicit (prettyM $ first (const ()) pat)) <> "."
    , bold "Expected:" PP.<+> "an" PP.<+> dullGreen "explicit" PP.<+> "pattern."
    ]
