{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Elaboration.Match where

import Protolude

import Control.Monad
import Control.Monad.Trans.Maybe
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector (Vector)
import qualified Data.Vector as Vector

import {-# SOURCE #-} Elaboration.TypeCheck.Expr
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import qualified Effect.Log as Log
import Elaboration.Constraint
import Elaboration.Constructor
import Elaboration.MetaVar
import Elaboration.MetaVar.Zonk
import Elaboration.Monad
import Elaboration.TypeCheck.Literal
import Elaboration.Unify
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Literal as Core
import qualified Syntax.Pre.Literal as Pre
import qualified Syntax.Pre.Scoped as Pre
import Util

matchClauses
  :: Foldable t
  => Vector FreeVar
  -> t (Pre.Clause Pre.Expr FreeVar)
  -> Polytype
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
matchClauses vars preClauses typ k = do
  ctx <- getContext
  let
    clauses = foreach (toList preClauses) $ \(Pre.Clause pats rhs) ->
      Clause
        { _matches =
          toList $ Vector.zipWith (\v (_, pat) -> Match (pure v) (desugarPatLits pat) $ Context.lookupType v ctx) vars $ indexedPatterns pats
        , _rhs = rhs
        }
  match Config
    { _targetType = typ
    , _clauses = clauses
    , _coveredLits = mempty
    }
    k

matchBranches
  :: CoreM
  -> CoreM
  -> [(Pre.Pat (HashSet QConstr) Pre.Literal (PatternScope Pre.Expr FreeVar) (), PatternScope Pre.Expr FreeVar)]
  -> Polytype
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
matchBranches expr exprType [] typ _ = do
  -- Instead of supporting impossible patterns, we treat branchless case
  -- expressions a little specially so we can use
  --
  -- f x = case x of
  --
  -- when x is uninhabited.
  u <- uninhabited exprType
  if u then
    return $ Core.Case expr (ConBranches []) typ
  else
    panic "TODO error message"
matchBranches (Core.varView -> Just var) exprType brs typ k =
  match Config
    { _targetType = typ
    , _clauses =
      [ Clause
        { _matches = [Match (pure var) (imap (\i _ -> PatternVar i) $ desugarPatLits pat) exprType]
        , _rhs = rhs
        }
      | (pat, rhs) <- brs
      ]
    , _coveredLits = mempty
    }
    k
matchBranches expr exprType brs typ k =
  Context.freshExtend (binding "matchvar" Explicit exprType) $ \var -> do
    result <- matchBranches (pure var) exprType brs typ k
    Core.let_ (pure (var, noSourceLoc "match", expr)) result

uninhabited :: CoreM -> Elaborate Bool
uninhabited typ = do
  typ' <- whnf typ
  case Core.appsView typ' of
    (Core.Global typeName, _) -> do
      def <- fetchDefinition typeName
      return $ case def of
        ConstantDefinition {} -> False
        DataDefinition (DataDef _ constrDefs) _ -> null constrDefs
    _ -> return False

matchSingle
  :: FreeVar
  -> Pre.Pat (HashSet QConstr) Pre.Literal (PatternScope Pre.Expr FreeVar) ()
  -> PatternScope Pre.Expr FreeVar
  -> Polytype
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
matchSingle v pat body typ k = do
  varType <- Context.lookupType v
  match Config
    { _targetType = typ
    , _clauses =
      [ Clause
        { _matches = [Match (pure v) (PatternVar . fst <$> indexed (desugarPatLits pat)) varType]
        , _rhs = body
        }
      ]
    , _coveredLits = mempty
    }
    k

desugarPatLits
  :: Pre.Pat (HashSet QConstr) Pre.Literal typ v
  -> Pre.Pat (HashSet QConstr) Core.Literal typ v
desugarPatLits = Pre.bindPatLits litPat

-------------------------------------------------------------------------------

type PrePat = Pre.Pat (HashSet QConstr) Core.Literal (PatternScope Pre.Type FreeVar) PatternVar

data Config = Config
  { _targetType :: CoreM
  , _clauses :: [Clause]
  , _coveredLits :: !CoveredLits
  }

type CoveredLits = HashSet (FreeVar, Core.Literal)

data Clause = Clause
  { _matches :: [Match]
  , _rhs :: PatternScope Pre.Expr FreeVar
  }

data Match = Match CoreM PrePat CoreM

prettyClause :: Clause -> Elaborate Doc
prettyClause (Clause matches rhs) = do
  cs <- pretty <$> traverse prettyMatch matches
  e <- pretty . instantiate (pure . ("α" <>) . pretty . unPatternVar) <$> traverse prettyVar rhs
  return $ cs <> " ~> " <> e

prettyMatch :: Match -> Elaborate Doc
prettyMatch (Match e p t) = do
  pe <- prettyMeta =<< zonk e
  let
    pp = pretty
      $ bimap (const ()) (\(PatternVar i) -> "α" <> pretty i) p
  pt <- prettyMeta =<< zonk t
  return $ pe <> " / " <> pp <> " : " <> pt

-------------------------------------------------------------------------------

match
  :: Config
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
match config k = Log.indent $ do
  logPretty "tc.match.context" "context" $ Context.prettyContext $ prettyMeta <=< zonk
  logMeta "tc.match" "targetType" $ zonk $ _targetType config
  logPretty "tc.match" "clauses" $ traverse prettyClause $ _clauses config
  clauses <- catMaybes <$> mapM (simplifyClause $ _coveredLits config) (_clauses config)
  case clauses of
    [] -> do
      reportLocated $ PP.vcat
        [ "Non-exhaustive patterns"
        ]
      return $ Builtin.Fail $ _targetType config
    firstClause:clauses' -> do
      logPretty "tc.match" "firstClause" $ prettyClause firstClause
      let
        matches' = _matches firstClause
        config' = config { _clauses = firstClause : clauses' }
      case findConMatches matches' of
        (x, Left qc, typ):_ -> do
          logPretty "tc.match" "found con" $ pure qc
          splitCon config' x qc typ k
        (x, Right l, typ):_ -> do
          logPretty "tc.match" "found lit" $ pure l
          splitLit config' x l typ k
        [] -> do
          logCategory "tc.match" "found no con"
          case solved matches' of
            Just sub -> do
              logCategory "tc.match" "solved"
              instantiateSubst sub (_rhs firstClause) $ \e ->
                k e $ _targetType config
            Nothing ->
              panic "tc.match no solution"

findConMatches
  :: [Match]
  -> [(FreeVar, Either (HashSet QConstr) Core.Literal, CoreM)]
findConMatches matches
  = catMaybes
  $ foreach matches
  $ \case
    Match (Core.Var x) (Pre.unPatLoc -> Pre.ConPat qc _) typ ->
      Just (x, Left qc, typ)
    Match (Core.Var x) (Pre.unPatLoc -> Pre.LitPat l) typ ->
      Just (x, Right l, typ)
    Match {} ->
      Nothing

splitCon
  :: Config
  -> FreeVar
  -> HashSet QConstr
  -> CoreM
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
splitCon config x qcs typ k = do
  qc <- resolveConstr qcs $ Just typ
  logPretty "tc.match" "splitCon" $ pure qc
  let
    typeName = qconstrTypeName qc
  logPretty "tc.match.context" "splitCon context" $ Context.prettyContext prettyMeta
  def <- fetchDefinition $ gname typeName
  case def of
    ConstantDefinition {} -> panic "splitCon ConstantDefinition"
    DataDefinition (DataDef paramsTele constrDefs) _ -> do
      ctx <- getContext
      case Context.splitAt x ctx of
        Nothing -> panic "splitCon couldn't split context"
        Just (ctx1, b, ctx2) -> do
          params <- modifyContext (const ctx1) $ forTeleWithPrefixM paramsTele $ \h p s params -> do
            v <- exists h p $ instantiateTele snd params s
            return (p, v)
          runUnify (unify [] (Core.apps (global $ gname typeName) params) typ) report
          branches <- forM constrDefs $ \(ConstrDef c constrScope) -> do
            let
              constrType_ = instantiateTele snd params constrScope
            args <- forTeleWithPrefixM (Core.piTelescope constrType_) $ \h p s args -> do
              let t = instantiateTele (pure . fst) args s
              v <- Context.freeVar
              return (v, binding h p t)

            let
              plicitArgs = (\(v, Context.Binding _ p _ _) -> (p, pure v)) <$> args
              implicitParams = first implicitise <$> params
              val
                = Core.apps (Core.Con (QConstr typeName c))
                $ implicitParams <> plicitArgs
              ctx' =
                  ctx1
                  <> Context.fromList (toList args)
                  <> Context.fromList [(x, b { Context._value = Just val })]
                  <> ctx2
            modifyContext (const ctx') $ do
              branch <- match config k
              conBranch (QConstr typeName c) (fst <$> args) branch
          return $ Core.Case (pure x) (ConBranches branches) $ _targetType config

splitLit
  :: Config
  -> FreeVar
  -> Core.Literal
  -> CoreM
  -> (Pre.Expr FreeVar -> Polytype -> Elaborate CoreM)
  -> Elaborate CoreM
splitLit config x lit typ k = do
  let
    litType = inferCoreLit lit
  runUnify (unify [] litType typ) report
  branch <- Context.set x (Core.Lit lit) $ match config k
  defBranch <- match config
    { _coveredLits = _coveredLits config <> HashSet.singleton (x, lit)
    }
    k
  return
    $ Core.Case (pure x) (LitBranches (pure $ LitBranch lit branch) defBranch)
    $ _targetType config

simplifyClause :: CoveredLits -> Clause -> Elaborate (Maybe Clause)
simplifyClause coveredLits (Clause matches rhs) = Log.indent $ do
  logPretty "tc.match.simplify" "clause" $ prettyClause $ Clause matches rhs
  mmatches <- runMaybeT $
    concat <$> mapM (simplifyMatch coveredLits) matches
  case mmatches of
    Nothing -> do
      logShow "tc.match.simplify" "Nothing" ()
      return Nothing
    Just matches' -> do
      logPretty "tc.match.simplify" "clause'" $ prettyClause $ Clause matches' rhs
      maybeExpanded <- runMaybeT $
        expandAnnos mempty matches'
      case maybeExpanded of
        Nothing -> return $ Just $ Clause matches' rhs
        Just expanded -> simplifyClause coveredLits $ Clause expanded rhs


simplifyMatch :: CoveredLits -> Match -> MaybeT Elaborate [Match]
simplifyMatch coveredLits m@(Match expr pat typ) = do
  ctx <- getContext
  case (expr, pat) of
    (_, Pre.WildcardPat) -> return []
    (Core.Lit l1, Pre.LitPat l2)
      | l1 == l2 -> return []
      | otherwise -> fail "Literal mismatch"
    (Core.Var v, Pre.LitPat lit)
      | HashSet.member (v, lit) coveredLits -> fail "Literal already covered"
    (Core.Var v, _)
      | Just expr' <- Context.lookupValue v ctx ->
        simplifyMatch coveredLits $ Match expr' pat typ
    (Core.appsView -> (Core.Con qc, pes), Pre.ConPat qcs pats)
      | qc `HashSet.member` qcs -> do
        paramsTele <- lift $ fetchTypeParamsTele $ gname $ qconstrTypeName qc
        conType <- fetchQConstructor qc
        let
          tele = Core.piTelescope conType
          numParams = teleLength paramsTele
          exprs = toVector $ snd <$> pes
          types = forTele tele $ \_ _ s -> instantiateTele identity exprs s
          argTypes = Vector.drop numParams types
          argExprs = Vector.drop numParams exprs
          argPlics = Vector.drop numParams $ telePlics tele
        equalisedPats <- lift $ Vector.fromList <$> exactlyEqualisePats (toList argPlics) (toList pats)
        let
          matches = Vector.zipWith3 Match argExprs (snd <$> equalisedPats) argTypes
        concat <$> mapM (simplifyMatch coveredLits) matches
      | otherwise -> fail "Constructor mismatch"
    (_, Pre.PatLoc loc pat') -> do
      res <- located loc $ simplifyMatch coveredLits $ Match expr pat' typ
      return $ case res of
        [Match expr'' pat'' typ''] -> [Match expr'' (Pre.PatLoc loc pat'') typ'']
        _ -> res
    (Core.SourceLoc _ expr', _) -> simplifyMatch coveredLits $ Match expr' pat typ
    _ -> return [m]

expandAnnos
  :: PatSubst
  -> [Match]
  -> MaybeT Elaborate [Match]
expandAnnos _ [] = fail "expanded nothing"
expandAnnos sub (c:cs) = case matchSubst c of
  Nothing -> case c of
    Match expr (Pre.AnnoPat pat annoScope) typ -> do
      annoType' <- instantiateSubst sub annoScope $ \annoType ->
        lift $ checkPoly annoType Builtin.Type
      runUnify (unify [] annoType' typ) report
      return $ Match expr pat typ : cs
    _ -> fail "couldn't create subst for prefix"
  Just sub' -> (c:) <$> expandAnnos (sub' <> sub) cs

fetchTypeParamsTele :: GName -> Elaborate (Telescope (Core.Expr m) v)
fetchTypeParamsTele n = do
  def <- fetchDefinition n
  case def of
    ConstantDefinition {} -> panic "typeParamsTele ConstantDefinition"
    DataDefinition (DataDef paramsTele _) _ -> return paramsTele

matchSubst :: Match -> Maybe PatSubst
matchSubst (Match expr (Pre.VarPat _ pv) typ) = return $ HashMap.singleton pv (expr, typ)
matchSubst (Match expr (Pre.PatLoc _ pat) typ) = matchSubst $ Match expr pat typ
matchSubst _ = Nothing

solved :: [Match] -> Maybe PatSubst
solved = fmap mconcat . traverse matchSubst

-------------------------------------------------------------------------------

type PatSubst = HashMap PatternVar (CoreM, CoreM)

instantiateSubst
  :: (Eq b, Hashable b, Monad e, MonadContext CoreM m, MonadFresh m)
  => HashMap b (CoreM, CoreM)
  -> Scope b e FreeVar
  -> (e FreeVar -> m CoreM)
  -> m CoreM
instantiateSubst sub scope k = do
  let
    varSub = HashMap.mapMaybe (Core.varView . fst) sub
    exprSub = HashMap.difference sub varSub
  if HashMap.null exprSub then
    k $ instantiate (pure . (varSub HashMap.!)) scope
  else do
    let
      exprVec = toVector $ HashMap.toList exprSub
    Context.freshExtends
      (foreach exprVec $ \(_, (e, t)) -> Context.Binding mempty Explicit t $ Just e) $ \vs -> do
        let
          varSub' = varSub <> toHashMap (Vector.zipWith (\(p, _) v -> (p, v)) exprVec vs)
          vsSet = toHashSet vs
        e <- k $ instantiate (pure . (varSub' HashMap.!)) scope
        ctx <- getContext
        return
          $ e >>= \v ->
            if HashSet.member v vsSet then
              fromMaybe (pure v) $ Context.lookupValue v ctx
            else
              pure v

--------------------------------------------------------------------------------
-- "Equalisation" -- making the patterns match a list of parameter plicitnesses
-- by adding implicits
exactlyEqualisePats
  :: (Pretty c, Pretty l)
  => [Plicitness]
  -> [(Plicitness, Pre.Pat c l e v)]
  -> Elaborate [(Plicitness, Pre.Pat c l e v)]
exactlyEqualisePats [] [] = return []
exactlyEqualisePats [] ((p, pat):_) = do
  reportLocated
    $ PP.vcat
      [ "Too many patterns for type"
      , "Found the pattern:" PP.<+> red (pretty $ prettyAnnotation p (prettyM $ bimap (const ()) (const ()) pat)) <> "." -- TODO var printing
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
  :: (Pretty c, Pretty l)
  => [Plicitness]
  -> [(Plicitness, Pre.Pat c l e v)]
  -> Elaborate [(Plicitness, Pre.Pat c l e v)]
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

reportExpectedExplicit :: (Pretty c, Pretty l) => Pre.Pat c l e v -> Elaborate ()
reportExpectedExplicit pat
  = reportLocated
  $ PP.vcat
    [ "Explicit/implicit mismatch"
    , "Found the implicit pattern:" PP.<+> red (pretty $ prettyAnnotation Implicit (prettyM $ bimap (const ()) (const ()) pat)) <> "." -- TODO var printing
    , bold "Expected:" PP.<+> "an" PP.<+> dullGreen "explicit" PP.<+> "pattern."
    ]
