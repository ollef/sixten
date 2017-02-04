{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RecursiveDo, TypeFamilies #-}
module Backend.ClosureConvert where

import Control.Applicative
import Control.Monad.Except
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin
import Meta
import Syntax
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Converted as Converted
import TCM
import Util

type Meta = MetaVar Unit
type LExprM = Closed.Expr Meta
type LBrsM = Branches QConstr () Closed.Expr Meta

type CExprM = Converted.Expr Meta
type CBrsM = Branches QConstr () Converted.Expr Meta

createSignature
  :: LExprM
  -> TCM (Converted.Signature Converted.Expr Closed.Expr Meta)
createSignature sizedExpr@(Closed.Sized sz expr)  = case expr of
  Closed.Lams tele lamScope -> do
    (retDir, tele') <- createLambdaSignature tele lamScope
    return $ Converted.Function (NonClosureDir retDir) tele' lamScope
  _ -> return $ Converted.Constant (Closed.sizeDir sz) sizedExpr
createSignature _ = throwError "createSignature sizeless definition"

createLambdaSignature
  :: Telescope () Closed.Expr Void
  -> Scope Tele Closed.Expr Void
  -> TCM
    ( Direction
    , Telescope Direction Converted.Expr Void
    )
createLambdaSignature tele lamScope = mdo
  tele' <- forMTele tele $ \h () s -> do
    let e = instantiateTele pure vs $ vacuous s
    v <- forall h () Unit
    e' <- convertExpr e
    return (v, e')
  let vs = fst <$> tele'
      abstr = teleAbstraction vs
      tele'' = error "convertLambda" <$> Telescope ((\(v, e) -> (metaHint v, Converted.sizeDir e, abstract abstr e)) <$> tele')
  return (Closed.sExprDir $ fromScope lamScope, tele'')

convertSignature
  :: Converted.Signature Converted.Expr Closed.Expr Void
  -> TCM CExprM
convertSignature sig = case sig of
  Converted.Function retDir tele lamScope -> do
    vs <- forMTele tele $ \h _ _ -> forall h () Unit
    let lamExpr = instantiateTele pure vs $ vacuous lamScope
        abstr = teleAbstraction vs
    lamExpr' <- convertExpr lamExpr
    let lamScope' = abstract abstr lamExpr'
    return
      $ Converted.Sized (Converted.Lit 1) $ Converted.Lams retDir tele
      $ error "convertBody" <$> lamScope'
  Converted.Constant _ e -> convertExpr $ error "convertBody" <$> e

convertLambda
  :: Telescope () Closed.Expr Void
  -> Scope Tele Closed.Expr Void
  -> TCM
    ( Direction
    , Telescope Direction Converted.Expr Void
    , Scope Tele Converted.Expr Void
    )
convertLambda tele lamScope = mdo
  tele' <- forMTele tele $ \h () s -> do
    let e = instantiateTele pure vs $ vacuous s
    v <- forall h () Unit
    e' <- convertExpr e
    return (v, e')
  let vs = fst <$> tele'
      lamExpr = instantiateTele pure vs $ vacuous lamScope
      abstr = teleAbstraction vs
      tele'' = error "convertLambda" <$> Telescope ((\(v, e) -> (metaHint v, Converted.sizeDir e, abstract abstr e)) <$> tele')
  lamExpr' <- convertExpr lamExpr
  let lamScope' = abstract abstr lamExpr'
  return (Converted.sExprDir lamExpr', tele'', error "convertLambda" <$> lamScope')

convertExpr :: LExprM -> TCM CExprM
convertExpr expr = case expr of
  Closed.Var v -> return $ Converted.Var v
  Closed.Global g -> do
    sig <- convertedSignature g
    case sig of
      Converted.Function retDir tele _ -> return $ knownCall (Converted.Global g) retDir tele mempty
      _ -> return $ Converted.Global g
  Closed.Lit l -> return $ Converted.Lit l
  Closed.Con qc es -> Converted.Con qc <$> mapM convertExpr es
  Closed.Lams tele s -> do
    (retDir, tele', s') <- convertLambda tele s
    let cdir = NonClosureDir retDir
    return $ knownCall (Converted.Lams cdir tele' s') cdir tele' mempty
  Closed.Call (Closed.Global g) es -> do
    es' <- mapM convertExpr es
    sig <- convertedSignature g
    case sig of
      Converted.Function retDir tele _ -> return $ knownCall (Converted.Global g) retDir tele es'
      _ -> throwError $ "convertExpr call global " ++ show g
  Closed.Call (Closed.Lams tele s) es -> do
    (retDir, tele', s') <- convertLambda tele s
    es' <- mapM convertExpr es
    let cdir = NonClosureDir retDir
    return $ knownCall (Converted.Lams cdir tele' s') cdir tele' es'
  Closed.Call e es -> do
    e' <- convertExpr e
    es' <- mapM convertExpr es
    return $ unknownCall e' es'
  Closed.Let h e bodyScope -> do
    e' <- convertExpr e
    v <- forall h () Unit
    let bodyExpr = Util.instantiate1 (pure v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    let bodyScope' = abstract1 v bodyExpr'
    return $ Converted.Let h e' bodyScope'
  Closed.Case e brs -> Converted.Case <$> convertExpr e <*> convertBranches brs
  Closed.Prim p -> Converted.Prim <$> mapM convertExpr p
  Closed.Sized sz e -> Converted.Sized <$> convertExpr sz <*> convertExpr e

unknownCall
  :: CExprM
  -> Vector CExprM
  -> CExprM
unknownCall e es
  = Converted.Call ClosureDir (Converted.Global $ Builtin.applyName $ Vector.length es)
  $ Vector.cons (Converted.sized 1 e, Direct) $ (\sz -> (sz, Direct)) <$> Converted.sizedSizesOf es <|> (\arg -> (arg, Indirect)) <$> es

knownCall
  :: Converted.Expr Void
  -> ClosureDir
  -> Telescope Direction Converted.Expr Void
  -> Vector CExprM
  -> CExprM
knownCall f retDir tele args
  | numArgs < arity
    = Converted.Con Builtin.Ref
    $ pure
    $ Converted.Sized (Builtin.addSizes $ Vector.cons (Converted.Lit 2) $ Converted.sizeOf <$> args)
    $ Converted.Con Builtin.Closure
    $ Vector.cons (Converted.sized 1 fNumArgs)
    $ Vector.cons (Converted.sized 1 $ Converted.Lit $ fromIntegral $ arity - numArgs) args
  | numArgs == arity
    = Converted.Call retDir (vacuous f) $ Vector.zip args $ teleAnnotations tele
  | otherwise = do
    let (xs, ys) = Vector.splitAt arity args
    unknownCall (Converted.Call retDir (vacuous f) $ Vector.zip xs $ teleAnnotations tele) ys
  where
    numArgs = Vector.length args
    arity = teleLength tele
    fNumArgs
      = Converted.Lams ClosureDir tele'
      $ toScope
      $ fmap B
      $ Converted.Case (Builtin.deref $ Converted.Var 0)
      $ ConBranches
      $ pure
        ( Builtin.Closure
        , Telescope $ Vector.cons (mempty, (), Builtin.slit 1)
                    $ Vector.cons (mempty, (), Builtin.slit 1) clArgs'
        , toScope $ Converted.Call retDir (vacuous f) (Vector.zip (fArgs1 <> fArgs2) $ teleAnnotations tele)
        )
      where
        clArgs = (\(h, d, s) -> (h, d, mapBound (+ 2) s)) <$> Vector.take numArgs (unTelescope tele)
        clArgs' = (\(h, _, s) -> (h, (), vacuous s)) <$> clArgs
        fArgs1 = Vector.zipWith
          Converted.Sized ((\(_, _, s) -> unvar F absurd <$> fromScope s) <$> clArgs)
                          (Converted.Var . B <$> Vector.enumFromN 2 numArgs)
        fArgs2 = Vector.zipWith Converted.Sized
          (Converted.Var . F <$> Vector.enumFromN 1 numXs)
          (Converted.Var . F <$> Vector.enumFromN (fromIntegral $ 1 + numXs) numXs)
        xs = Vector.drop numArgs $ teleNames tele
        numXs = Vector.length xs
        tele'
          = Telescope
          $ Vector.cons ("x_this", Direct, Builtin.slit 1)
          $ (\h -> (h, Direct, Builtin.slit 1)) <$> xs
          <|> (\(n, h) -> (h, Indirect, Builtin.svarb $ 1 + Tele n)) <$> Vector.indexed xs

convertBranches :: LBrsM -> TCM CBrsM
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    tele' <- forMTele tele $ \h () s -> do
      let e = instantiateTele pure vs s
      v <- forall h () Unit
      e' <- convertExpr e
      return (v, e')
    let vs = fst <$> tele'
        brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ (\(v, e) -> (metaHint v, (), abstract abstr e)) <$> tele'
    brExpr' <- convertExpr brExpr
    let brScope' = abstract abstr brExpr'
    return (qc, tele'', brScope')
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(l, e) -> (,) l <$> convertExpr e) lbrs <*> convertExpr def
