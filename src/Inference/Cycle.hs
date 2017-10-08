{-# LANGUAGE MonadComprehensions, OverloadedStrings #-}
module Inference.Cycle where

import Control.Monad.Except
import Data.Bitraversable
import Data.Foldable as Foldable
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Inference.Monad
import Meta
import Syntax
import Syntax.Abstract
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

detectDefCycles
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> Infer ()
detectDefCycles defs = do
  defExprs <- traverse
    (bitraverse pure zonk)
    [(v, e) | (_, (v, Definition _ _ e, _)) <- defs]
  let locMap = HashMap.fromList $ Vector.toList [(v, loc) | (loc, (v, _, _)) <- defs]
      recs =
        [ (v, unguardedOccurrences e)
        | (v, e) <- defExprs
        ]
  case cycles recs of
    firstCycle:_ -> do
      let headVar = head firstCycle
          loc = locMap HashMap.! headVar
          showVar v = showMeta (pure v :: AbstractM)
      printedHeadVar <- showVar headVar
      printedCycle <- mapM showVar $ drop 1 firstCycle ++ [headVar]
      throwError
        $ show (explain loc
          $ Err
            (Just "Circular definition")
            ([ "The definition of " <> Leijen.red printedHeadVar <> " is circular."
            , "It depends on " <> Leijen.dullblue (head printedCycle)
            ] ++
            ["which depends " <> Leijen.dullblue v' | v' <- drop 1 printedCycle]
            )
            mempty
            mempty)
    [] -> return ()

unguardedOccurrences
  :: Expr v
  -> [v]
unguardedOccurrences (Lam _ _ t _) = toList t
unguardedOccurrences e = toList e
