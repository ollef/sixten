{-# LANGUAGE MonadComprehensions, OverloadedStrings, ViewPatterns #-}
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
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Inference.Monad
import Inference.Meta
import Syntax
import Syntax.Abstract
import Util
import Util.TopoSort

detectTypeRepCycles
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> Infer ()
detectTypeRepCycles defs = do
  reps <- traverse
    (bitraverse pure zonk)
    [(v, rep) | (_, (v, DataDefinition _ rep, _)) <- defs]
  let locMap = HashMap.fromList $ Vector.toList [(v, loc) | (loc, (v, _, _)) <- defs]
  case cycles reps of
    firstCycle:_ -> do
      let headVar = head firstCycle
          loc = locMap HashMap.! headVar
          showVar v = showMeta (pure v :: AbstractM)
      printedHeadVar <- showVar headVar
      printedCycle <- mapM showVar $ drop 1 firstCycle ++ [headVar]
      throwError
        $ show (explain loc
          $ Err
            (Just "Type has potentially infinite memory representation")
            ([ "The size in memory of the type " <> Leijen.red printedHeadVar <> " might be infinite."
            , "Its size depends on the size of " <> Leijen.dullblue (head printedCycle)
            ] ++
            ["which depends on the size of " <> Leijen.dullblue v' | v' <- drop 1 printedCycle]
            )
            mempty
            mempty)
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
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> Infer ()
detectDefCycles defs = do
  (peeledDefExprs, locMap) <- peelLets [(loc, v, e) | (loc, (v, Definition _ _ e, _)) <- Vector.toList defs]
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
          let loc = locMap HashMap.! var
              showVar v = showMeta (pure v :: AbstractM)
              constantsInAllOccs = toHashSet expr `HashSet.intersection` constants
              functionsInImmAppOccs = possiblyImmediatelyAppliedVars expr `HashSet.intersection` functions
              circularOccs = constantsInAllOccs <> functionsInImmAppOccs
          unless (HashSet.null circularOccs) $ do
            printedVar <- showVar var
            printedOccs <- mapM showVar $ HashSet.toList circularOccs
            throwError
              $ show (explain loc
                $ Err
                  (Just "Circular definition")
                  [ "The definition of " <> Leijen.red printedVar <> " is circular."
                  , "It depends on " <> prettyHumanList "and" (Leijen.dullblue <$> printedOccs) <> " from the same binding group."
                  ]
                  mempty
                  mempty)

peelLets
  :: [(SourceLoc, MetaA, AbstractM)]
  -> Infer ([(MetaA, AbstractM)], HashMap MetaA SourceLoc)
peelLets = fmap fold . mapM go
  where
    go
     :: (SourceLoc, MetaA, Expr MetaA)
     -> Infer ([(MetaA, Expr MetaA)], HashMap MetaA SourceLoc)
    go (loc, v, e) = do
      e' <- zonk e
      case e' of
        Let ds scope -> do
          vs <- forMLet ds $ \h _ t ->
            forall h Explicit t
          let inst = instantiateLet pure vs
          es <- forMLet ds $ \_ s _ ->
            return $ inst s
          let ds' = (loc, v, inst scope) : Vector.toList (Vector.zipWith ((,,) loc) vs es)
          peelLets ds'
        _ -> return ([(v, e')], HashMap.singleton v loc)

possiblyImmediatelyAppliedVars
  :: (Eq v, Hashable v)
  => Expr v
  -> HashSet v
possiblyImmediatelyAppliedVars = go
  where
    go (Var _) = mempty
    go Lam {} = mempty
    go (appsView -> (Con _, xs)) = HashSet.unions [go x | (_, x) <- xs]
    go e = toHashSet e
