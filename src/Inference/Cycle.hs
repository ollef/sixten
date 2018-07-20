{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Inference.Cycle where

import Control.Monad.Except
import Data.Bitraversable
import Data.Foldable as Foldable
import Data.Hashable
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Error
import Inference.MetaVar
import Inference.MetaVar.Zonk
import Inference.Monad
import Syntax
import Syntax.Core
import Util
import Util.TopoSort
import VIX

detectTypeRepCycles
  :: Pretty name
  => Vector (FreeV, name, SourceLoc, Definition (Expr MetaVar) FreeV)
  -> Infer ()
detectTypeRepCycles defs = do
  reps <- traverse
    (bitraverse pure zonk)
    [(v, rep) | (v, _, _, DataDefinition _ rep) <- toList defs]
  let locMap = HashMap.fromList [(v, (name, loc)) | (v, name, loc, _) <- toList defs]
  case cycles reps of
    firstCycle:_ -> do
      let headVar = head firstCycle
          (headName, loc) = locMap HashMap.! headVar
      let printedCycle = map (pretty . fst . (locMap HashMap.!)) $ drop 1 firstCycle ++ [headVar]
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
  => Vector (FreeV, name, SourceLoc, Definition (Expr MetaVar) FreeV)
  -> Infer ()
detectDefCycles defs = do
  (peeledDefExprs, locMap) <- peelLets [(name, loc, v, e) | (v, name, loc, ConstantDefinition _ e) <- Vector.toList defs]
  forM_ (topoSortWith fst snd peeledDefExprs) $ \scc -> case scc of
    AcyclicSCC _ -> return ()
    CyclicSCC defExprs -> do
      let (functions, constants) = foldMap go defExprs
            where
              go (v, Lam {}) = (HashSet.singleton v, mempty)
              go (v, _) = (mempty, HashSet.singleton v)
      forM_ defExprs $ \(var, expr) -> case expr of
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
  :: [(name, SourceLoc, FreeV, CoreM)]
  -> Infer ([(FreeV, CoreM)], HashMap FreeV (name, SourceLoc))
peelLets = fmap fold . mapM go
  where
    go
     :: (name, SourceLoc, FreeV, CoreM)
     -> Infer ([(FreeV, CoreM)], HashMap FreeV (name, SourceLoc))
    go (name, loc, var, expr) = do
      expr' <- zonk expr
      case expr' of
        Let ds scope -> do
          vs <- forMLet ds $ \h _ t ->
            forall h Explicit t
          let inst = instantiateLet pure vs
          es <- forMLet ds $ \_ s _ ->
            return $ inst s
          let ds' = (name, loc, var, inst scope) : Vector.toList (Vector.zipWith (\v e -> (name, loc, v, e)) vs es)
          peelLets ds'
        _ -> return ([(var, expr')], HashMap.singleton var (name, loc))

possiblyImmediatelyAppliedVars
  :: (Eq v, Hashable v)
  => Expr m v
  -> HashSet v
possiblyImmediatelyAppliedVars = go
  where
    go (Var _) = mempty
    go Lam {} = mempty
    go (appsView -> (Con _, xs)) = HashSet.unions [go x | (_, x) <- xs]
    go e = toHashSet e
