{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module ClosureConvert where

import qualified Bound.Scope.Simple as Simple
import Control.Applicative
import Control.Monad.Except
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras

import Builtin
import Meta
import Syntax
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Converted as Converted
import TCM
import Util

data MetaData s = Unknown deriving Show
instance Show1 MetaData

type Meta = MetaVar MetaData
type LExprM s = Lifted.Expr (Meta s)
type LSExprM s = Lifted.SExpr (Meta s)
type LBrsM s = SimpleBranches QConstr Lifted.Expr (Meta s)

type CExprM s = Converted.Expr (Meta s)
type CSExprM s = Converted.SExpr (Meta s)
type CBrsM s = SimpleBranches QConstr Converted.Expr (Meta s)

sizeDir :: Converted.Expr v -> Direction
sizeDir (Converted.Lit 1) = Direct
sizeDir _ = Indirect

sExprDir :: Lifted.SExpr v -> Direction
sExprDir (Lifted.Sized (Lifted.Lit 1) _) = Direct
sExprDir _ = Indirect

convertSignature
  :: LSExprM s
  -> TCM s (Converted.Signature Lifted.SExpr (Meta s))
convertSignature expr = case expr of
  Lifted.Sized _ (Lifted.Lams tele lamScope) -> do
    (retDir, tele') <- convertLambdaSignature tele lamScope
    return $ Converted.Function retDir tele' lamScope
  _ -> return $ Converted.Constant expr

convertLambdaSignature
  :: Telescope Simple.Scope () Lifted.Expr Void
  -> Simple.Scope Tele Lifted.SExpr Void
  -> TCM s
    ( Direction
    , Telescope Simple.Scope Direction Converted.Expr Void
    )
convertLambdaSignature tele (Simple.Scope lamExpr) = mdo
  tele' <- forMTele tele $ \h () s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) $ vacuous s
    v <- forall_ h Unknown
    e' <- convertExpr e
    return (v, e')
  let vs = fst <$> tele'
      abstr = teleAbstraction vs
      tele'' = error "convertLambda" <$> Telescope ((\(v, e) -> (metaHint v, sizeDir e, Simple.abstract abstr e)) <$> tele')
  return (sExprDir lamExpr, tele'')

convertBody
  :: Converted.Signature Lifted.SExpr Void
  -> TCM s (CSExprM s)
convertBody sig = case sig of
  Converted.Function retDir tele lamScope -> do
    vs <- forMTele tele $ \h _ _ -> forall_ h Unknown
    let lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
        abstr = teleAbstraction vs
    lamExpr' <- convertSExpr lamExpr
    let lamScope' = Simple.abstract abstr lamExpr'
    return
      $ Converted.sized 1
      $ Converted.Lams retDir tele
      $ error "convertBody" <$> lamScope'
  Converted.Constant e -> convertSExpr $ error "convertBody" <$> e

convertLambda
  :: Telescope Simple.Scope () Lifted.Expr Void
  -> Simple.Scope Tele Lifted.SExpr Void
  -> TCM s
    ( Direction
    , Telescope Simple.Scope Direction Converted.Expr Void
    , Simple.Scope Tele Converted.SExpr Void
    )
convertLambda tele lamScope = mdo
  tele' <- forMTele tele $ \h () s -> do
    let e = instantiateVar ((vs Vector.!) . unTele) $ vacuous s
    v <- forall_ h Unknown
    e' <- convertExpr e
    return (v, e')
  let vs = fst <$> tele'
      lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
      abstr = teleAbstraction vs
      tele'' = error "convertLambda" <$> Telescope ((\(v, e) -> (metaHint v, sizeDir e, Simple.abstract abstr e)) <$> tele')
  lamExpr' <- convertSExpr lamExpr
  let lamScope' = Simple.abstract abstr lamExpr'
  return (sExprDir lamExpr, tele'', error "convertLambda" <$> lamScope')

convertExpr :: LExprM s -> TCM s (CExprM s)
convertExpr expr = case expr of
  Lifted.Var v -> return $ Converted.Var v
  Lifted.Global g -> do
    sig <- convertedSignature g
    case sig of
      Converted.Function retDir tele _ -> knownCall (Converted.Global g) retDir tele mempty
      _ -> return $ Converted.Global g
  Lifted.Lit l -> return $ Converted.Lit l
  Lifted.Con qc es -> Converted.Con qc <$> mapM convertSExpr es
  Lifted.Lams tele s -> do
    (retDir, tele', s') <- convertLambda tele s
    knownCall (Converted.Lams retDir tele' s') retDir tele' mempty
  Lifted.Call (Lifted.Global g) es -> do
    es' <- mapM convertSExpr es
    sig <- convertedSignature g
    case sig of
      Converted.Function retDir tele _ -> knownCall (Converted.Global g) retDir tele es'
      _ -> throwError $ "convertExpr call global " ++ show g
  Lifted.Call (Lifted.Lams tele s) es -> do
    (retDir, tele', s') <- convertLambda tele s
    es' <- mapM convertSExpr es
    knownCall (Converted.Lams retDir tele' s') retDir tele' es'
  Lifted.Call e es -> do
    e' <- convertExpr e
    es' <- mapM convertSExpr es
    unknownCall e' es'
  Lifted.Let h e bodyScope -> do
    e' <- convertSExpr e
    v <- forall_ h Unknown
    let bodyExpr = instantiateVar (\() -> v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    let bodyScope' = Simple.abstract1 v bodyExpr'
    return $ Converted.Let h e' bodyScope'
  Lifted.Case e brs -> Converted.Case <$> convertSExpr e <*> convertBranches brs
  Lifted.Prim p -> Converted.Prim <$> mapM convertExpr p

unknownCall
  :: CExprM s
  -> Vector (CSExprM s)
  -> TCM s (CExprM s)
unknownCall e es = return
  $ Converted.Call Indirect (Converted.Global $ Builtin.applyName $ Vector.length es)
  $ Vector.cons (Converted.sized 1 e, Direct) $ (\sz -> (sz, Direct)) <$> Converted.sizedSizesOf es <|> (\arg -> (arg, Indirect)) <$> es

knownCall
  :: Converted.Expr Void
  -> Direction
  -> Telescope Simple.Scope Direction Converted.Expr Void
  -- -> Simple.Scope Tele Converted.SExpr Void
  -> Vector (CSExprM s)
  -> TCM s (CExprM s)
knownCall f retDir tele {- (Simple.Scope functionBody) -} args
  | numArgs < arity
    = return
    $ Converted.Con Builtin.Ref
    $ pure
    $ Converted.Sized (Builtin.addSizes $ Vector.cons (Converted.Lit 2) $ Converted.sizeOf <$> args)
    $ Converted.Con Builtin.Closure
    $ Vector.cons (Converted.sized 1 fNumArgs)
    $ Vector.cons (Converted.sized 1 $ Converted.Lit $ fromIntegral $ arity - numArgs) args
  | numArgs == arity
    = return
    $ Converted.Call retDir (vacuous f) $ Vector.zip args $ teleAnnotations tele
  | otherwise = do
    let (xs, ys) = Vector.splitAt arity args
    unknownCall (Converted.Call retDir (vacuous f) $ Vector.zip xs $ teleAnnotations tele) ys
  where
    numArgs = Vector.length args
    arity = teleLength tele
    fNumArgs
      = Converted.Lams Indirect tele'
      $ Simple.Scope
      $ fmap B
      -- $ Converted.Sized returnSize
      $ unknownSize
      $ Converted.Case (unknownSize $ Converted.Call Indirect (Converted.Global Builtin.DerefName) $ pure (Converted.sized 1 $ Converted.Var 0, Direct))
      $ SimpleConBranches
      $ pure
      ( Builtin.Closure
      , Telescope $ Vector.cons (mempty, (), Builtin.slit 1)
                  $ Vector.cons (mempty, (), Builtin.slit 1) clArgs'
      , Simple.Scope $ Converted.Call retDir (vacuous f) (Vector.zip (fArgs1 <> fArgs2) $ teleAnnotations tele)
      )
      where
        unknownSize = Converted.Sized $ Converted.Global "ClosureConvert.UnknownSize"
        clArgs = (\(h, d, s) -> (h, d, vacuous $ Simple.mapBound (+ 2) s)) <$> Vector.take numArgs (unTelescope tele)
        clArgs' = (\(h, _, s) -> (h, (), s)) <$> clArgs
        fArgs1 = Vector.zipWith
          Converted.Sized (Converted.Var . B <$> Vector.enumFromN 2 numArgs)
                          ((\(_, _, s) -> unvar F absurd <$> Simple.unscope s) <$> clArgs)
        fArgs2 = Vector.zipWith Converted.Sized
          (Converted.Var . F <$> Vector.enumFromN 1 numXs)
          (Converted.Var . F <$> Vector.enumFromN (fromIntegral $ 1 + numXs) numXs)
        xs = Vector.drop numArgs $ teleNames tele
        numXs = Vector.length xs
        tele'
          = Telescope
          $ Vector.cons (nameHint "x_this", Direct, Builtin.slit 1)
          $ (\h -> (h, Direct, Builtin.slit 1)) <$> xs
          <|> (\(n, h) -> (h, Indirect, Builtin.svarb $ 1 + Tele n)) <$> Vector.indexed xs
        {-
        fReturnSize = unvar id absurd <$> Converted.sizeOf functionBody
        returnSize
          = Converted.Case (unknownSize $ Converted.Call Indirect (Converted.Global Builtin.DerefName) $ pure (Converted.sized 1 $ Converted.Var 0, Direct))
          $ SimpleConBranches
          $ pure
          ( Builtin.Closure
          , Telescope $ Vector.cons (mempty, (), Builtin.slit 1)
                      $ Vector.cons (mempty, (), Builtin.slit 1) clArgs'
          , Simple.Scope $ fmap go fReturnSize
          )
        go n | unTele n < numArgs = B $ n + 2 -- from closure
             | otherwise = F $ n + fromIntegral (arity - numArgs) + 1 -- From function args
          -}

convertSExpr :: LSExprM s -> TCM s (CSExprM s)
convertSExpr (Lifted.Sized sz e) = Converted.Sized <$> convertExpr sz <*> convertExpr e

convertBranches :: LBrsM s -> TCM s (CBrsM s)
convertBranches (SimpleConBranches cbrs) = fmap SimpleConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h () s -> do
      let e = instantiateVar ((vs Vector.!) . unTele) s
      v <- forall_ h Unknown
      e' <- convertExpr e
      return (v, e')
    let vs = fst <$> tele'
        brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\(v, e) -> (metaHint v, (), Simple.abstract abstr e)) <$> tele'
    brExpr' <- convertExpr brExpr
    let brScope' = Simple.abstract abstr brExpr'
    return (qc, tele'', brScope')
convertBranches (SimpleLitBranches lbrs def) = SimpleLitBranches
  <$> mapM (\(l, e) -> (,) l <$> convertExpr e) lbrs <*> convertExpr def
