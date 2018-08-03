{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Analysis.Cycle where

import Control.Monad.Except
import Data.Foldable as Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector

import Error
import Syntax
import Syntax.Core
import FreeVar
import Util
import Util.TopoSort
import VIX

type FreeV = FreeVar Plicitness

cycleCheck
  :: [(QName, SourceLoc, Definition (Expr m) FreeV, Expr m FreeV)]
  -> VIX ()
cycleCheck defs = do
  vs <- forM defs $ \(name, _loc, _def, _typ) ->
    freeVar (fromQName name) Explicit
  let lookupName
        = hashedLookup
        $ toVector
        $ zipWith (\(name, _, _, _) v -> (name, v)) defs vs
      expose g = maybe (global g) pure $ lookupName g
      exposedDefs = do
        (v, (name, loc, def, _typ)) <- zip vs defs
        let def' = gbound expose def
        return (v, name, loc, def')
  detectTypeRepCycles exposedDefs
  detectDefCycles exposedDefs

detectTypeRepCycles
  :: Pretty name
  => [(FreeV, name, SourceLoc, Definition (Expr m) FreeV)]
  -> VIX ()
detectTypeRepCycles defs = do
  let reps = [(v, rep) | (v, _, _, DataDefinition _ rep) <- defs]
  let locMap = HashMap.fromList [(v, (name, loc)) | (v, name, loc, _) <- defs]
  case cycles reps of
    firstCycle:_ -> do
      let headVar = head firstCycle
          (headName, loc) = locMap HashMap.! headVar
          printedCycle = map (pretty . fst . (locMap HashMap.!)) $ drop 1 firstCycle ++ [headVar]
      report
        $ TypeError
          "Type has potentially infinite memory representation"
          (Just loc)
          $ PP.vcat
            ([ "The size in memory of the type " <> red (pretty headName) <> " might be infinite."
            , "Its size depends on the size of " <> dullBlue (head printedCycle)
            ] ++
            ["which depends on the size of " <> dullBlue v' | v' <- drop 1 printedCycle]
            )
    [] -> return ()

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
detectDefCycles
  :: Pretty name
  => [(FreeV, name, SourceLoc, Definition (Expr m) FreeV)]
  -> VIX ()
detectDefCycles defs = do
  (peeledDefExprs, locMap) <- peelLets [(name, loc, v, e) | (v, name, loc, ConstantDefinition _ e) <- defs]
  forM_ (topoSortWith fst snd peeledDefExprs) $ \scc -> case scc of
    AcyclicSCC _ -> return ()
    CyclicSCC defExprs -> do
      let (functions, constants) = foldMap go defExprs
            where
              go (v, unSourceLoc -> Lam {}) = (HashSet.singleton v, mempty)
              go (v, _) = (mempty, HashSet.singleton v)
      forM_ defExprs $ \(var, expr) -> case unSourceLoc expr of
        Lam {} -> return ()
        _ -> do
          let (name, loc) = locMap HashMap.! var
              constantsInAllOccs = toHashSet expr `HashSet.intersection` constants
              functionsInImmAppOccs = possiblyImmediatelyAppliedVars expr `HashSet.intersection` functions
              circularOccs = constantsInAllOccs <> functionsInImmAppOccs
          unless (HashSet.null circularOccs) $ do
            let printedOccs = map pretty $ HashSet.toList circularOccs
            report
              $ TypeError
                "Circular definition"
                (Just loc)
                $ PP.vcat
                  [ "The definition of " <> red (pretty name) <> " is circular."
                  , "It depends on " <> prettyHumanList "and" (dullBlue <$> printedOccs) <> " from the same binding group."
                  ]

peelLets
  :: [(name, SourceLoc, FreeV, Expr m FreeV)]
  -> VIX ([(FreeV, Expr m FreeV)], HashMap FreeV (name, SourceLoc))
peelLets = fmap fold . mapM go
  where
    go
     :: (name, SourceLoc, FreeV, Expr m FreeV)
     -> VIX ([(FreeV, Expr m FreeV)], HashMap FreeV (name, SourceLoc))
    go (name, loc, var, expr) = case unSourceLoc expr of
      Let ds scope -> do
        vs <- forMLet ds $ \h _ _ ->
          freeVar h Explicit
        let inst = instantiateLet pure vs
        es <- forMLet ds $ \_ s _ ->
          return $ inst s
        let ds' = (name, loc, var, inst scope) : Vector.toList (Vector.zipWith (\v e -> (name, loc, v, e)) vs es)
        peelLets ds'
      _ -> return ([(var, expr)], HashMap.singleton var (name, loc))

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
