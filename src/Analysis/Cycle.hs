{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Analysis.Cycle where

import Protolude hiding (TypeError)

import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin.Names as Builtin
import Effect
import Error
import Syntax
import Syntax.Core
import TypedFreeVar
import Util
import Util.TopoSort
import VIX

-- We need to detect possible cycles in top-level constants because if not,
-- we'll accept e.g. the following program:
--
-- i = f MkUnit
-- f MkUnit = i
--
-- This would be fine (but loop) in a lazy setting but using CBV and our
-- compilation scheme where constants are initialised at program startup, this
-- actually means that i gets some default value like 0. (i is compiled to a
-- memory cell that's initially zero, then initialized to the result of `f
-- MkUnit` at program startup, but `f MkUnit` will just read i's memory cell,
-- which is zero).
--
-- Functions are allowed to be mutually recursive; only constants are affected.
--
-- The vanilla approach is to restrict the use of definitions in the same
-- binding group when defining constants.
--
-- We additionally allow the use of _functions_ from the same binding group if
-- they're definitely not immediately _applied_ in the definition of the
-- constant. The reason we do this is that class instances often end up on
-- safe-but-not-vanilla forms like `inst = let f = ... inst ... in MkClass f`.
--
-- So when is x definitely not immediately applied in the definition of c?
--
-- Either x doesn't occur free in c at all, or c is of one of the following
-- forms:
--
-- c = Con as   where x is definitely not applied in as
-- c = \y. e
-- c = x
--
-- We also peel off any lets at the top-level of all definitions and include
-- them in the analysis.

-- cycleCheckGroup
--   :: Vector (QName, SourceLoc, ClosedDefinition Expr, Biclosed Expr)
--   -> VIX (Vector (QName, SourceLoc, ClosedDefinition Expr, Biclosed Expr))
-- cycleCheckGroup defs = do
--   defs' <- cycleCheck [(x, loc, def, typ) | (x, loc, ClosedDefinition def, Biclosed typ) <- defs]
--   return $ do
--     (x, loc, def, typ) <- defs'
--     return
--       ( x
--       , loc
--       , closeDefinition identity (panic "cycleCheckGroup close def") def
--       , biclose identity (panic "cycleCheckGroup close typ") typ
--       )

type FreeV m = FreeVar Plicitness (Expr m)

cycleCheck
  :: Vector (GName, SourceLoc, ClosedDefinition Expr, Biclosed Expr)
  -> VIX (Vector (GName, SourceLoc, ClosedDefinition Expr, Biclosed Expr))
cycleCheck defs = do
  vs <- forM defs $ \(name, _loc, _, Biclosed typ) -> do
    typ' <- cycleCheckExpr typ
    freeVar (fromGName name) Explicit typ'
  defs' <- forM defs $ \(name, loc, ClosedDefinition def, _) -> located loc $ do
    def' <- cycleCheckDef def
    return (name, loc, def')
  let nameVarVec
        = Vector.zipWith (\(name, _, _) v -> (name, v)) defs' vs
      lookupName = hashedLookup nameVarVec
      expose g = maybe (global g) pure $ lookupName g
      exposedDefs = do
        (v, (name, loc, def)) <- Vector.zip vs defs'
        let def' = gbound expose def
        return (v, name, loc, def')
  cycleCheckTypeReps exposedDefs
  exposedDefs' <- cycleCheckLets exposedDefs
  let lookupVar = hashedLookup $ (\(n, v) -> (v, n)) <$> nameVarVec
      unexpose v = maybe (pure v) global $ lookupVar v
  return $ do
    (v, name, loc, def) <- exposedDefs'
    let def' = def >>>= unexpose
    return
      ( name
      , loc
      , closeDefinition identity (panic "cycleCheck close def'") def'
      , biclose identity (panic "cycleCheck close typ") $ varType v
      )

cycleCheckDef
  :: Definition (Expr Void) (FreeV m)
  -> VIX (Definition (Expr m) (FreeV m))
cycleCheckDef (ConstantDefinition a e)
  = ConstantDefinition a <$> cycleCheckExpr e
cycleCheckDef (DataDefinition (DataDef params constrs) rep) = do
  vs <- forTeleWithPrefixM params $ \h p s vs -> do
    t <- cycleCheckExpr $ instantiateTele pure vs s
    freeVar h p t
  constrs' <- forM constrs $ \cdef ->
    forM cdef $ \s ->
      cycleCheckExpr $ instantiateTele pure vs s
  rep' <- cycleCheckExpr rep
  return $ DataDefinition (dataDef vs constrs') rep'

cycleCheckExpr
  :: Expr Void (FreeV m)
  -> VIX (Expr m (FreeV m))
cycleCheckExpr expr = case expr of
    Var v -> return $ Var v
    Meta m _ -> absurd m
    Global g -> return $ Global g
    Lit l -> return $ Lit l
    Pi h p t s -> absCase h p t s pi_
    Lam h p t s -> absCase h p t s lam
    Con qc -> return $ Con qc
    App e1 p e2 -> App
      <$> cycleCheckExpr e1
      <*> pure p
      <*> cycleCheckExpr e2
    Case e brs retType -> Case
      <$> cycleCheckExpr e
      <*> cycleCheckBranches brs
      <*> cycleCheckExpr retType
    Let ds bodyScope -> do
      vs <- forMLet ds $ \h _ _ t -> do
        t' <- cycleCheckExpr t
        freeVar h Explicit t'
      ds' <- iforMLet ds $ \i h loc s _ -> located loc $ do
        let e = instantiateLet pure vs s
        e' <- cycleCheckExpr e
        return (vs Vector.! i, fromNameHint "(no name)" identity h, loc, ConstantDefinition Concrete e')
      body <- cycleCheckExpr $ instantiateLet pure vs bodyScope
      ds'' <- cycleCheckLets ds'
      let ds''' =
            [ (v, loc, e)
            | (v, _, loc, def) <- ds''
            , let ConstantDefinition _ e = def
            ]
      return $ let_ ds''' body
    ExternCode c retType -> ExternCode
      <$> mapM cycleCheckExpr c
      <*> cycleCheckExpr retType
    SourceLoc loc e -> located loc $ SourceLoc loc <$> cycleCheckExpr e
    where
      absCase h p t s c = do
        t' <- cycleCheckExpr t
        v <- freeVar h p t'
        e <- cycleCheckExpr $ instantiate1 (pure v) s
        return $ c v e

cycleCheckBranches
  :: Branches Plicitness (Expr Void) (FreeV m)
  -> VIX (Branches Plicitness (Expr m) (FreeV m))
cycleCheckBranches (ConBranches cbrs) = ConBranches <$> do
  forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forTeleWithPrefixM tele $ \h p s vs -> do
      t <- cycleCheckExpr $ instantiateTele pure vs s
      freeVar h p t
    brExpr <- cycleCheckExpr $ instantiateTele pure vs brScope
    return $ conBranchTyped c vs brExpr
cycleCheckBranches (LitBranches lbrs d) = do
  lbrs' <- forM lbrs $ \(LitBranch l e) -> LitBranch l <$> cycleCheckExpr e
  d' <- cycleCheckExpr d
  return $ LitBranches lbrs' d'

cycleCheckTypeReps
  :: Pretty name
  => Vector (FreeV m, name, SourceLoc, Definition (Expr m) (FreeV m))
  -> VIX ()
cycleCheckTypeReps defs = do
  let reps = flip Vector.mapMaybe defs $ \(v, _, _, def) -> case def of
        DataDefinition _ rep -> Just (v, rep)
        _ -> Nothing
  let locMap = toHashMap [(v, (name, loc)) | (v, name, loc, _) <- defs]
  case cycles reps of
    firstCycle:_ -> do
      let headVar = unsafeHead firstCycle
          (headName, loc) = locMap HashMap.! headVar
          printedCycle = map (pretty . fst . (locMap HashMap.!)) $ drop 1 firstCycle ++ [headVar]
      report
        $ TypeError
          "Type has potentially infinite memory representation"
          (Just loc)
          $ PP.vcat
            ([ "The size in memory of the type " <> red (pretty headName) <> " might be infinite."
            , "Its size depends on the size of " <> dullBlue (unsafeHead printedCycle)
            ] ++
            ["which depends on the size of " <> dullBlue v' | v' <- drop 1 printedCycle]
            )
    [] -> return ()
  where
    unsafeHead = fromMaybe (panic "cycleCheckTypeReps") . head

cycleCheckLets
  :: Pretty name
  => Vector (FreeV m, name, SourceLoc, Definition (Expr m) (FreeV m))
  -> VIX (Vector (FreeV m, name, SourceLoc, Definition (Expr m) (FreeV m)))
cycleCheckLets defs = do
  (peeledDefExprs, locMap) <- peelLets
    $ flip Vector.mapMaybe defs $ \(v, name, loc, def) -> case def of
      ConstantDefinition _ e -> Just (name, loc, v, e)
      _ -> Nothing
  Any cyclic <- foldForM (topoSortWith fst snd peeledDefExprs) $ \case
    AcyclicSCC _ -> return mempty
    CyclicSCC defExprs -> do
      let (functions, constants) = foldMap go defExprs
            where
              go (v, unSourceLoc -> Lam {}) = (HashSet.singleton v, mempty)
              go (v, _) = (mempty, HashSet.singleton v)
      foldForM defExprs $ \(var, expr) -> case unSourceLoc expr of
        Lam {} -> return mempty
        _ -> do
          let (name, loc) = locMap HashMap.! var
              constantsInAllOccs = toHashSet expr `HashSet.intersection` constants
              functionsInImmAppOccs = possiblyImmediatelyAppliedVars expr `HashSet.intersection` functions
              circularOccs = constantsInAllOccs <> functionsInImmAppOccs
          if HashSet.null circularOccs then
            return mempty
          else do
            let printedOccs = map pretty $ HashSet.toList circularOccs
            report
              $ TypeError
                "Circular definition"
                (Just loc)
                $ PP.vcat
                  [ "The definition of " <> red (pretty name) <> " is circular."
                  , "It depends on " <> prettyHumanList "and" (dullBlue <$> printedOccs) <> " from the same binding group."
                  ]
            return $ Any True
  return $ if cyclic then
    -- TODO use actual error message
    [ (v, name, loc, ConstantDefinition Abstract $ Builtin.Fail $ varType v)
    | (v, name, loc, _) <- defs
    ]
  else
    defs
  where
    foldForM xs = fmap fold . forM xs


peelLets
  :: Vector (name, SourceLoc, FreeV m, Expr m (FreeV m))
  -> VIX (Vector (FreeV m, Expr m (FreeV m)), HashMap (FreeV m) (name, SourceLoc))
peelLets = fmap fold . mapM go
  where
    go
     :: (name, SourceLoc, FreeV m, Expr m (FreeV m))
     -> VIX (Vector (FreeV m, Expr m (FreeV m)), HashMap (FreeV m) (name, SourceLoc))
    go (name, loc, var, expr) = case unSourceLoc expr of
      Let ds scope -> do
        vs <- forMLet ds $ \h _ _ t ->
          freeVar h Explicit t
        let inst = instantiateLet pure vs
        es <- forMLet ds $ \_ _ s _ ->
          return $ inst s
        let ds'
              = pure (name, loc, var, inst scope)
              <> Vector.zipWith (\v e -> (name, loc, v, e)) vs es
        peelLets ds'
      _ -> return (pure (var, expr), HashMap.singleton var (name, loc))

possiblyImmediatelyAppliedVars
  :: (Eq v, Hashable v)
  => Expr m v
  -> HashSet v
possiblyImmediatelyAppliedVars = go
  where
    go (unSourceLoc -> Var _) = mempty
    go (unSourceLoc -> Lam {}) = mempty
    go (appsView -> (unSourceLoc -> Con _, xs)) = HashSet.unions [go x | (_, x) <- xs]
    go e = toHashSet e
