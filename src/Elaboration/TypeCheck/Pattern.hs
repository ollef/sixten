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
import Effect.Context as Context
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
import Util

data ExpectedPat
  = InferPat (IORef CoreM)
  | CheckPat CoreM

data BindingType = WildcardBinding | VarBinding
  deriving (Eq, Show)

instance Pretty BindingType where pretty = shower

type PatVars = Vector (BindingType, FreeVar)
type BoundPatVars = Vector FreeVar

boundPatVars :: PatVars -> BoundPatVars
boundPatVars = fmap snd . Vector.filter ((== VarBinding) . fst)

checkPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) ()
  -> BoundPatVars
  -> Polytype
  -> (Core.Pat CoreM FreeVar -> CoreM -> PatVars -> Elaborate a)
  -> Elaborate a
checkPat p pat vs expectedType = tcPat p pat vs $ CheckPat expectedType

inferPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) ()
  -> (Core.Pat CoreM FreeVar -> CoreM -> PatVars -> Polytype -> Elaborate a)
  -> Elaborate a
inferPat p pat k = do
  ref <- liftIO $ newIORef $ panic "inferPat: empty result"
  tcPat p pat mempty (InferPat ref) $ \pat' patExpr vs -> do
    t <- liftIO $ readIORef ref
    k pat' patExpr vs t

tcPats
  :: Vector (Plicitness, Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) ())
  -> BoundPatVars
  -> Telescope (Core.Expr MetaVar) FreeVar
  -> (Vector (Core.Pat CoreM FreeVar, CoreM, CoreM) -> PatVars -> Elaborate a)
  -> Elaborate a
tcPats pats vs tele k = do
  unless (Vector.length pats == teleLength tele)
    $ panic "tcPats length mismatch"

  results <- iforTeleWithPrefixM tele $ \i _ _ s results -> do
    let
      argExprs = snd3 . fst <$> results
      expectedType = instantiateTele identity argExprs s
      (p, pat) = pats Vector.! i
      -- TODO could be more efficient
      varPrefix = snd =<< results
      vs' = vs <> boundPatVars varPrefix
    logShow "tc.pat" "tcPats vars" vs'
    (pat', patExpr, vs'') <- checkPat p pat vs' expectedType k
    return ((pat', patExpr, expectedType), vs'')

  return (fst <$> results, snd =<< results)

tcPat
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) ()
  -> BoundPatVars
  -> ExpectedPat
  -> (Core.Pat CoreM FreeVar -> CoreM -> PatVars -> Elaborate a)
  -> Elaborate a
tcPat p pat vs expected k =
  -- logPretty "tc.pat" "tcPat" $ pure $ first (pretty . fmap pretty . instantiatePattern pure vs) pat
  -- logPretty "tc.pat" "tcPat vs" $ pure vs
  Log.indent $ tcPat' p pat vs expected $ \pat' patExpr vs' -> do
    -- logPretty "tc.pat" "tcPat vs res" $ pure vs'
    logMeta "tc.pat" "tcPat patExpr" $ zonk patExpr
    k pat' patExpr vs'

tcPat'
  :: Plicitness
  -> Pre.Pat (HashSet QConstr) (PatternScope Pre.Expr FreeVar) ()
  -> BoundPatVars
  -> ExpectedPat
  -> (Core.Pat CoreM FreeVar -> CoreM -> PatVars -> Elaborate a)
  -> Elaborate a
tcPat' p pat vs expected k = case pat of
  Pre.VarPat h () -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType h
        liftIO $ writeIORef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    Context.freshExtend (binding h p expectedType) $ \v ->
      k (Core.VarPat h v) (pure v) (pure (VarBinding, v))
  Pre.WildcardPat -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType "_"
        liftIO $ writeIORef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    Context.freshExtend (binding "_" p expectedType) $ \v ->
      k (Core.VarPat "_" v) (pure v) (pure (WildcardBinding, v))
  Pre.LitPat lit -> do
    let
      (expr, typ) = inferLit lit
      pat' = litPat lit
    (pat'', expr') <- instPatExpected expected typ pat' expr
    k pat'' expr' mempty
  Pre.ConPat cons pats -> do
    qc@(QConstr typeName _) <- resolveConstr cons $ case expected of
      CheckPat expectedType -> Just expectedType
      InferPat _ -> Nothing
    def <- fetchDefinition $ gname typeName
    case def of
      ConstantDefinition {} -> panic "tcPat' ConstantDefinition"
      DataDefinition (DataDef paramsTele _) _ -> do
        conType <- fetchQConstructor qc

        let
          numParams = teleLength paramsTele
          (tele, retScope) = Core.pisView conType
          argPlics = Vector.drop numParams $ telePlics tele

        pats' <- Vector.fromList <$> exactlyEqualisePats (Vector.toList argPlics) (Vector.toList pats)

        paramVars <- forTeleWithPrefixM paramsTele $ \h p' s paramVars ->
          exists h p' $ instantiateTele identity paramVars s

        let argTele = instantiatePrefix paramVars tele

        tcPats pats' vs argTele $ \pats'' vs' -> do

          let
            argExprs = snd3 <$> pats''
            argTypes = thd3 <$> pats''
            pats''' = Vector.zip3 argPlics (fst3 <$> pats'') argTypes
            params = Vector.zip (telePlics paramsTele) paramVars
            iparams = first implicitise <$> params
            patExpr = Core.apps (Core.Con qc) $ iparams <> Vector.zip argPlics argExprs

            retType = instantiateTele identity (paramVars <|> argExprs) retScope

          (pat', patExpr') <- instPatExpected expected retType (Core.ConPat qc params pats''') patExpr

          k pat' patExpr' vs'
  Pre.AnnoPat pat' s -> do
    let
      patType = instantiatePattern pure vs s
    patType' <- checkPoly patType Builtin.Type
    checkPat p pat' vs patType' $ \pat'' patExpr vs' -> do
      (pat''', patExpr') <- instPatExpected expected patType' pat'' patExpr
      k pat''' patExpr' vs'
  Pre.ViewPat _ _ -> panic "tcPat ViewPat undefined TODO"
  Pre.PatLoc loc pat' -> located loc $
    tcPat' p pat' vs expected $ \pat'' patExpr vs' ->
      k pat'' (Core.SourceLoc loc patExpr) vs'

instPatExpected
  :: ExpectedPat
  -> Polytype -- ^ patType
  -> Core.Pat CoreM FreeVar -- ^ pat
  -> CoreM -- ^ :: patType
  -> Elaborate (Core.Pat CoreM FreeVar, CoreM) -- ^ (pat :: expectedType, :: expectedType)
instPatExpected (CheckPat expectedType) patType pat patExpr = do
  f <- subtype expectedType patType
  viewPat expectedType pat patExpr f
instPatExpected (InferPat ref) patType pat patExpr = do
  liftIO $ writeIORef ref patType
  return (pat, patExpr)

viewPat
  :: CoreM -- ^ expectedType
  -> Core.Pat CoreM FreeVar -- ^ pat
  -> CoreM -- ^ :: patType
  -> (CoreM -> CoreM) -- ^ expectedType -> patType
  -> Elaborate (Core.Pat CoreM FreeVar, CoreM) -- ^ (expectedType, :: expectedType)
viewPat expectedType pat patExpr f =
  Context.freshExtend (binding mempty Explicit expectedType) $ \x -> do
    let fx = f $ pure x
    if fx == pure x then
      return (pat, patExpr)
    else do
      fExpr <- Core.lam x fx
      return (Core.ViewPat fExpr pat, pure x)

patToTerm
  :: Core.Pat CoreM FreeVar
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
