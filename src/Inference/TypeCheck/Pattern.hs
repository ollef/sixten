{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Inference.TypeCheck.Pattern where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.ST
import Data.Bifunctor
import Data.HashSet(HashSet)
import Data.Monoid
import Data.STRef
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Inference.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Inference.Constructor
import Inference.MetaVar
import Inference.Monad
import Inference.Subtype
import Inference.TypeOf
import MonadContext
import Syntax
import qualified Syntax.Abstract as Abstract
import Syntax.Abstract.Pattern as Abstract
import qualified Syntax.Concrete.Scoped as Concrete
import TypedFreeVar
import Util
import VIX

data ExpectedPat
  = InferPat (STRef RealWorld AbstractM)
  | CheckPat AbstractM

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
  -> Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) ()
  -> BoundPatVars
  -> Polytype
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM, PatVars)
checkPat p pat vs expectedType = tcPat p pat vs $ CheckPat expectedType

inferPat
  :: Plicitness
  -> Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) ()
  -> BoundPatVars
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM, PatVars, Polytype)
inferPat p pat vs = do
  ref <- liftST $ newSTRef $ error "inferPat: empty result"
  (pat', patExpr, vs') <- tcPat p pat vs $ InferPat ref
  t <- liftST $ readSTRef ref
  return (pat', patExpr, vs', t)

tcPats
  :: Vector (Plicitness, Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) ())
  -> BoundPatVars
  -> Telescope Plicitness (Abstract.Expr MetaVar) FreeV
  -> Infer (Vector (Abstract.Pat AbstractM FreeV, AbstractM, AbstractM), PatVars)
tcPats pats vs tele = do
  unless (Vector.length pats == teleLength tele)
    $ internalError "tcPats length mismatch"

  results <- iforTeleWithPrefixM tele $ \i _ _ s results -> do
    let argExprs = snd3 . fst <$> results
        expectedType = instantiateTele id argExprs s
        (p, pat) = pats Vector.! i
        -- TODO could be more efficient
        varPrefix = join (snd <$> results)
        vs' = vs <> boundPatVars varPrefix
    logShow 30 "tcPats vars" (varId <$> vs')
    (pat', patExpr, vs'') <- withPatVars varPrefix $ checkPat p pat vs' expectedType
    return ((pat', patExpr, expectedType), vs'')

  return (fst <$> results, join (snd <$> results))

tcPat
  :: Plicitness
  -> Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) ()
  -> BoundPatVars
  -> ExpectedPat
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM, PatVars)
tcPat p pat vs expected = do
  whenVerbose 20 $ do
    let shownPat = first (pretty . fmap pretty . instantiatePattern pure vs) pat
    logPretty 20 "tcPat" shownPat
  logPretty 30 "tcPat vs" vs
  (pat', patExpr, vs') <- indentLog $ tcPat' p pat vs expected
  whenVerbose 20 $ do
    let shownPat' = first show pat'
    logShow 20 "tcPat res" shownPat'
  logPretty 30 "tcPat vs res" vs'
  return (pat', patExpr, vs')

tcPat'
  :: Plicitness
  -> Concrete.Pat (HashSet QConstr) (PatternScope Concrete.Expr FreeV) ()
  -> BoundPatVars
  -> ExpectedPat
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM, PatVars)
tcPat' p pat vs expected = case pat of
  Concrete.VarPat h () -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType h
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall h p expectedType
    return (Abstract.VarPat h v, pure v, pure (VarBinding, v))
  Concrete.WildcardPat -> do
    expectedType <- case expected of
      InferPat ref -> do
        expectedType <- existsType "_"
        liftST $ writeSTRef ref expectedType
        return expectedType
      CheckPat expectedType -> return expectedType
    v <- forall "_" p expectedType
    return (Abstract.VarPat "_" v, pure v, pure (WildcardBinding, v))
  Concrete.LitPat lit -> do
    (pat', expr) <- instPatExpected
      expected
      (typeOfLiteral lit)
      (LitPat lit)
      (Abstract.Lit lit)
    return (pat', expr, mempty)
  Concrete.ConPat cons pats -> do
    qc@(QConstr typeName _) <- resolveConstr cons $ case expected of
      CheckPat expectedType -> Just expectedType
      InferPat _ -> Nothing
    (_, typeType) <- definition typeName
    conType <- qconstructor qc

    let paramsTele = Abstract.telescope typeType
        numParams = teleLength paramsTele
        (tele, retScope) = Abstract.pisView conType
        argPlics = Vector.drop numParams $ teleAnnotations tele

    pats' <- Vector.fromList <$> exactlyEqualisePats (Vector.toList argPlics) (Vector.toList pats)

    paramVars <- forTeleWithPrefixM paramsTele $ \h p' s paramVars ->
      exists h p' $ instantiateTele id paramVars s

    let argTele = instantiatePrefix paramVars tele

    (pats'', vs') <- tcPats pats' vs argTele

    let argExprs = snd3 <$> pats''
        argTypes = thd3 <$> pats''
        pats''' = Vector.zip3 argPlics (fst3 <$> pats'') argTypes
        params = Vector.zip (teleAnnotations paramsTele) paramVars
        iparams = first implicitise <$> params
        patExpr = Abstract.apps (Abstract.Con qc) $ iparams <> Vector.zip argPlics argExprs

        retType = instantiateTele id (paramVars <|> argExprs) retScope

    (pat', patExpr') <- instPatExpected expected retType (Abstract.ConPat qc params pats''') patExpr

    return (pat', patExpr', vs')
  Concrete.AnnoPat pat' s -> do
    let patType = instantiatePattern pure vs s
    patType' <- checkPoly patType Builtin.Type
    (pat'', patExpr, vs') <- checkPat p pat' vs patType'
    (pat''', patExpr') <- instPatExpected expected patType' pat'' patExpr
    return (pat''', patExpr', vs')
  Concrete.ViewPat _ _ -> internalError "tcPat ViewPat undefined TODO"
  Concrete.PatLoc loc pat' -> located loc $ tcPat' p pat' vs expected

instPatExpected
  :: ExpectedPat
  -> Polytype -- ^ patType
  -> Abstract.Pat AbstractM FreeV -- ^ pat
  -> AbstractM -- ^ :: patType
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM) -- ^ (pat :: expectedType, :: expectedType)
instPatExpected (CheckPat expectedType) patType pat patExpr = do
  f <- subtype expectedType patType
  viewPat expectedType pat patExpr f
instPatExpected (InferPat ref) patType pat patExpr = do
  liftST $ writeSTRef ref patType
  return (pat, patExpr)

viewPat
  :: AbstractM -- ^ expectedType
  -> Abstract.Pat AbstractM FreeV -- ^ pat
  -> AbstractM -- ^ :: patType
  -> (AbstractM -> Infer AbstractM) -- ^ expectedType -> patType
  -> Infer (Abstract.Pat AbstractM FreeV, AbstractM) -- ^ (expectedType, :: expectedType)
viewPat expectedType pat patExpr f = do
  x <- forall mempty Explicit expectedType
  fx <- f $ pure x
  if fx == pure x then
    return (pat, patExpr)
  else do
    let fExpr = Abstract.Lam mempty Explicit expectedType $ abstract1 x fx
    return (Abstract.ViewPat fExpr pat, pure x)

patToTerm
  :: Abstract.Pat AbstractM FreeV
  -> Infer (Maybe AbstractM)
patToTerm pat = case pat of
  Abstract.VarPat _ v -> return $ Just $ Abstract.Var v
  Abstract.ConPat qc params pats -> do
    mterms <- mapM (\(p, pat', _typ') -> fmap ((,) p) <$> patToTerm pat') pats
    case sequence mterms of
      Nothing -> return Nothing
      Just terms -> return $ Just $
        Abstract.apps (Abstract.Con qc) $ params <> terms
  Abstract.LitPat l -> return $ Just $ Abstract.Lit l
  Abstract.ViewPat{} -> return Nothing

--------------------------------------------------------------------------------
-- "Equalisation" -- making the patterns match a list of parameter plicitnesses
-- by adding implicits
exactlyEqualisePats
  :: Pretty c
  => [Plicitness]
  -> [(Plicitness, Concrete.Pat c e ())]
  -> Infer [(Plicitness, Concrete.Pat c e ())]
exactlyEqualisePats [] [] = return []
exactlyEqualisePats [] ((p, pat):_)
  = throwLocated
  $ PP.vcat
    [ "Too many patterns for type"
    , "Found the pattern:" PP.<+> red (runPrettyM $ prettyAnnotation p (prettyM $ first (const ()) pat)) <> "."
    , bold "Expected:" PP.<+> "no more patterns."
    ]
exactlyEqualisePats (Constraint:ps) ((Constraint, pat):pats)
  = (:) (Implicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Constraint:ps) pats
  = (:) (Constraint, Concrete.WildcardPat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Implicit:ps) pats
  = (:) (Implicit, Concrete.WildcardPat) <$> exactlyEqualisePats ps pats
exactlyEqualisePats (Explicit:_) ((Constraint, pat):_)
  = throwExpectedExplicit pat
exactlyEqualisePats (Explicit:_) ((Implicit, pat):_)
  = throwExpectedExplicit pat
exactlyEqualisePats (Explicit:_) []
  = throwLocated
  $ PP.vcat
    [ "Not enough patterns for type"
    , "Found the pattern: no patterns."
    , bold "Expected:" PP.<+> "an explicit pattern."
    ]

equalisePats
  :: (Pretty c)
  => [Plicitness]
  -> [(Plicitness, Concrete.Pat c e ())]
  -> Infer [(Plicitness, Concrete.Pat c e ())]
equalisePats _ [] = return []
equalisePats [] pats = return pats
equalisePats (Constraint:ps) ((Constraint, pat):pats)
  = (:) (Constraint, pat) <$> equalisePats ps pats
equalisePats (Implicit:ps) ((Implicit, pat):pats)
  = (:) (Implicit, pat) <$> equalisePats ps pats
equalisePats (Explicit:ps) ((Explicit, pat):pats)
  = (:) (Explicit, pat) <$> equalisePats ps pats
equalisePats (Constraint:ps) pats
  = (:) (Constraint, Concrete.WildcardPat) <$> equalisePats ps pats
equalisePats (Implicit:ps) pats
  = (:) (Implicit, Concrete.WildcardPat) <$> equalisePats ps pats
equalisePats (Explicit:_) ((Implicit, pat):_)
  = throwExpectedExplicit pat
equalisePats (Explicit:_) ((Constraint, pat):_)
  = throwExpectedExplicit pat

throwExpectedExplicit :: (Pretty v, Pretty c) => Concrete.Pat c e v -> Infer a
throwExpectedExplicit pat
  = throwLocated
  $ PP.vcat
    [ "Explicit/implicit mismatch"
    , "Found the implicit pattern:" PP.<+> red (runPrettyM $ prettyAnnotation Implicit (prettyM $ first (const ()) pat)) <> "."
    , bold "Expected:" PP.<+> "an" PP.<+> dullGreen "explicit" PP.<+> "pattern."
    ]
