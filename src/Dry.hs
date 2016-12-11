{-# LANGUAGE MonadComprehensions #-}
module Dry where

import Control.Monad.RWS
import Data.Bifunctor
import Data.Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.HashMap.Lazy(HashMap)
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin
import Syntax
import Syntax.Concrete.Pattern
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Wet as Wet
import Util
import TopoSort

type Dry = RWS (Constr -> HashSet Name) () (HashSet Name)

runDry :: Dry a -> (Constr -> HashSet Name) -> (a, HashSet Name)
runDry m constrDefs = (a, s)
  where
    (a, s, ~()) = runRWS m constrDefs mempty

dryProgram
  :: HashMap Name (SourceLoc, Wet.Definition Name, Wet.Type Name)
  -> [[(Name, SourceLoc, Concrete.PatDefinition Concrete.Expr Void, Concrete.Type Void)]]
dryProgram defs = do
  let driedDefDeps = for (HashMap.toList defs) $ \(n, (loc, def, typ)) -> do
        let (def', defDeps) = runDry (dryDefinition def) lookupConstr
            (typ', typDeps) = runDry (dryExpr typ) lookupConstr
        (n, (loc, def', typ'), toHashSet def' <> toHashSet typ' <> defDeps <> typDeps)
  let defDeps = for driedDefDeps $ \(n, _, deps) -> (n, deps)
      driedDefs = HashMap.fromList $ for driedDefDeps $ \(n, def, _) -> (n, def)
  let sortedDeps = topoSort defDeps
  for sortedDeps $ \ns -> for ns $ \n -> do
    let (loc, def, typ) = driedDefs HashMap.! n
    (n, loc, bound global global def, bind global global typ)
  where
    constrs = unions $
      [ HashMap.singleton c $ HashSet.singleton n
      | (n, (_, Wet.DataDefinition _ d, _)) <- HashMap.toList defs
      , c <- constrName <$> d
      ] <>
      [ HashMap.singleton c $ HashSet.singleton n
      | (n, (DataDefinition d, _)) <- HashMap.toList Builtin.contextP
      , c <- constrNames d
      ]
    lookupConstr c = HashMap.lookupDefault mempty c constrs

    union = HashMap.unionWith HashSet.union
    unions = foldl' union mempty

    for = flip map

dryDefinition
  :: Wet.Definition Name
  -> Dry (Concrete.PatDefinition Concrete.Expr Name)
dryDefinition (Wet.Definition defLines) = do
  let defLinesWithArity = [(defLine, Wet.defLineArity defLine) | defLine <- defLines]
      arity = maximum $ snd <$> defLinesWithArity
  Concrete.PatDefinition <$> mapM (dryDefLine arity) defLinesWithArity
dryDefinition (Wet.DataDefinition params cs) = do
  let paramNames = (\(_, n, _) -> n) <$> params
      abstr = abstract $ teleAbstraction $ Vector.fromList paramNames
  Concrete.PatDataDefinition . DataDef <$> mapM (mapM (fmap abstr . dryExpr)) cs

dryDefLine
  :: Int
  -> (Wet.DefLine Name, Int)
  -> Dry (Concrete.DefLine Concrete.Expr Name)
dryDefLine arity (Wet.DefLine plicitPats e, patsArity) = do
  plicitPats' <- traverse (traverse dryPat) plicitPats

  let pats = snd <$> plicitPats'
      vars = Vector.concat $ toVector <$> pats
      typedPats'' = Vector.fromList
        $ second void <$> abstractPatternsTypes vars plicitPats'

  -- TODO handle different plicitness in eta expansion
  Concrete.etaExpandDefLine (patsArity - arity) Explicit
    . Concrete.DefLine typedPats''
    . abstract (patternAbstraction vars) <$> dryExpr e

dryExpr
  :: Wet.Expr Name
  -> Dry (Concrete.Expr Name)
dryExpr expr = case expr of
  Wet.Var v -> do
    let c = fromName v
    defs <- asks ($ c)
    if HashSet.null defs then
      return $ Concrete.Var v
    else do
      modify $ mappend defs
      return $ Concrete.Con $ Left c
  Wet.Global v -> return $ Concrete.Global v
  Wet.Lit l -> return $ Concrete.Lit l
  Wet.Pi p pat e -> do
    pat' <- dryPat pat
    let vs = toVector pat'
    Concrete.Pi p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> dryExpr e
  Wet.Lam p pat e -> do
    pat' <- dryPat pat
    let vs = toVector pat'
    Concrete.Lam p (void $ abstractPatternTypes vs pat')
      . abstract (patternAbstraction vs) <$> dryExpr e
  Wet.App e1 p e2 -> Concrete.App
    <$> dryExpr e1
    <*> pure p
    <*> dryExpr e2
  Wet.Case e pats -> Concrete.Case
    <$> dryExpr e
    <*> mapM (uncurry dryBranch) pats
  Wet.Wildcard -> return Concrete.Wildcard
  Wet.SourceLoc loc e -> Concrete.SourceLoc loc <$> dryExpr e

dryBranch
  :: Pat (Wet.Expr Name) Name
  -> Wet.Expr Name
  -> Dry (Pat (PatternScope Concrete.Expr Name) (), PatternScope Concrete.Expr Name)
dryBranch pat e = do
  pat' <- dryPat pat
  let vs = toVector pat'
  (,) (void $ abstractPatternTypes vs pat') . abstract (patternAbstraction vs) <$> dryExpr e

dryPat
  :: Pat (Wet.Expr Name) Name
  -> Dry (Pat (Concrete.Expr Name) Name)
dryPat pat = case pat of
  VarPat h v -> do
    let c = fromName v
    defs <- asks ($ c)
    if HashSet.null defs then
      return $ VarPat h v
    else do
      modify $ mappend defs
      return $ ConPat (Left c) mempty
  WildcardPat -> return WildcardPat
  LitPat l -> return $ LitPat l
  ConPat con ps -> do
    case con of
      Left c -> do
        defs <- asks ($ c)
        modify $ mappend defs
      Right (QConstr n _) ->
        modify $ HashSet.insert n
    ConPat con <$> mapM (\(p, pat') -> (,) p <$> dryPat pat') ps
  AnnoPat t p -> AnnoPat <$> dryExpr t <*> dryPat p
  ViewPat t p -> ViewPat <$> dryExpr t <*> dryPat p
  PatLoc loc p -> PatLoc loc <$> dryPat p
