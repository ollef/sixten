{-# LANGUAGE BangPatterns, MonadComprehensions, OverloadedStrings #-}
module Inference.Cycle where

import Data.Foldable as Foldable
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
import VIX
import Util.TopoSort

detectTypeRepCycles
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> VIX ()
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
            mempty)
    [] -> return ()

detectDefCycles
  :: Vector (SourceLoc, (MetaA, Definition Expr MetaA, AbstractM))
  -> VIX ()
detectDefCycles defs = do
  defExprs <- traverse
    (bitraverse pure zonk)
    [(v, e) | (_, (v, Definition e, _)) <- defs]
  let locMap = HashMap.fromList $ Vector.toList [(v, loc) | (loc, (v, _, _)) <- defs]
      recs =
        [ (v, fmap fst $ filter ((== 0) . snd) $ occurrenceDepths e)
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
            mempty)
    [] -> return ()

occurrenceDepths
  :: Expr v
  -> [(v, Int)]
occurrenceDepths = go 0 . fmap Just
  where
    inst = instantiate (const $ pure Nothing)
    go !d expr = case expr of
      Var Nothing -> []
      Var (Just v) -> [(v, d)]
      Global _ -> []
      Con _ -> []
      Lit _ -> []
      Pi _ _ t s -> go d t <> go d (inst s)
      Lam _ _ t s -> go d t <> go (d + 1) (inst s)
      App e1 _ e2 -> go d e1 <> go d e2
      Let _ e s -> go d e <> go d (inst s)
      Case e brs retType -> go d e <> go d retType <> case brs of
        ConBranches cbrs -> concat
          [ go d (inst scope) <> concat [ go d $ inst s | (_, _, s) <- tele ]
          | (_, Telescope tele, scope) <- cbrs
          ]
        LitBranches lbrs def -> concat
          [ go d e'
          | (_, e') <- lbrs
          ]
          <> go d def
      ExternCode c t -> (Foldable.toList c >>= go d) <> go d t
