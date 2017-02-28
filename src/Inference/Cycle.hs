{-# LANGUAGE MonadComprehensions, OverloadedStrings #-}
module Inference.Cycle where

import qualified Data.Vector as Vector
import Control.Monad.Except
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid
import Data.Vector(Vector)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen
import Text.Trifecta.Result(Err(Err), explain)

import Meta
import Syntax
import Syntax.Abstract
import TCM
import TopoSort

detectTypeRepCycles
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> TCM ()
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
            (Just "Type has non-finite memory representation")
            ([ "The size in memory of the type " <> Leijen.red printedHeadVar <> " is infinite."
            , "Its size depends on the size of " <> Leijen.dullblue (head printedCycle)
            ] ++
            ["which depends on the size of " <> Leijen.dullblue v' | v' <- drop 1 printedCycle]
            )
            mempty)
    [] -> return ()
