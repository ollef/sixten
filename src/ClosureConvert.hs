{-# LANGUAGE OverloadedStrings, RecursiveDo #-}
module ClosureConvert where

import qualified Bound.Scope.Simple as Simple
import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Builtin
import Meta
import Syntax
import Syntax.Lifted
import TCM
import Util

type Meta = MetaVar Expr
type ExprM s = Expr (Meta s)
type SExprM s = SExpr (Meta s)
type BrsM s = SimpleBranches QConstr Expr (Meta s)

convertBody :: ExprM s -> TCM s (ExprM s)
convertBody expr = case expr of
  Lams tele lamScope -> mdo
    tele' <- forMSimpleTele tele $ \h s -> do
      let e = instantiateVar ((vs Vector.!) . unTele) $ vacuous s
      v <- forall_ h e
      e' <- convertExpr e
      return (v, e')
    let vs = fst <$> tele'
        lamExpr = instantiateVar ((vs Vector.!) . unTele) $ vacuous lamScope
        abstr = teleAbstraction vs
        tele'' = SimpleTelescope $ bimap metaHint (Simple.abstract abstr) <$> tele'
    lamExpr' <- convertSExpr lamExpr
    let lamScope' = Simple.abstract abstr lamExpr'
    return $ Lams (error "convertBody" <$> tele'') (error "convertBody" <$> lamScope')
  _ -> convertExpr expr

convertExpr :: ExprM s -> TCM s (ExprM s)
convertExpr expr = case expr of
  Var v -> return $ Var v
  Global g -> do
    def <- liftedDefinition g
    case def of
      Sized _ (Lams tele s) -> knownCall (Global g) tele s mempty
      _ -> return $ Global g
  Lit l -> return $ Lit l
  Con qc es -> Con qc <$> mapM convertSExpr es
  Lams tele s -> knownCall (Lams tele s) tele s mempty
  Call (Global g) es -> do
    def <- liftedDefinition g
    case def of
      Sized _ (Lams tele s) -> knownCall (Global g) tele s es
      _ -> throwError $ "convertExpr Call Global " <> show (pretty $ show <$> expr)
  Call (Lams tele s) es -> knownCall (Lams tele s) tele s es
  Call e es -> unknownCall e es
  Let h e bodyScope -> do
    e' <- convertSExpr e
    v <- forall_ h $ sizeOf e'
    let bodyExpr = instantiateVar (\() -> v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    let bodyScope' = Simple.abstract1 v bodyExpr'
    return $ Let h e' bodyScope'
  Case e brs -> Case <$> convertSExpr e <*> convertBranches brs
  Prim p -> Prim <$> mapM convertExpr p

unknownCall
  :: ExprM s
  -> Vector (SExprM s)
  -> TCM s (ExprM s)
unknownCall e es
  = return
  $ Call (Global $ Builtin.apply $ Vector.length es)
  $ Vector.cons (sized 1 e) $ sizedSizesOf es <> es

knownCall
  :: Expr Void
  -> SimpleTelescope Expr Void
  -> Simple.Scope Tele SExpr Void
  -> Vector (SExprM s)
  -> TCM s (ExprM s)
knownCall f tele (Simple.Scope functionBody) args
  | numArgs < arity
    = return
    $ Con Builtin.Ref
    $ pure
    $ Sized (addSizes $ Vector.cons (Lit 2) $ sizeOf <$> args)
    $ Con Builtin.Closure
    $ Vector.cons (sized 1 fNumArgs)
    $ Vector.cons (sized 1 $ Lit $ fromIntegral $ arity - numArgs) args
  | numArgs == arity
    = return
    $ Call (vacuous f) args
  | otherwise = do
    let (xs, ys) = Vector.splitAt arity args
    unknownCall (Call (vacuous f) xs) ys
  where
    numArgs = Vector.length args
    arity = simpleTeleLength tele
    fNumArgs
      = Lams tele'
      $ Simple.Scope
      $ fmap B
      $ Sized returnSize
      $ Case (unknownSize $ Call (Global Builtin.DerefName) $ pure $ sized 1 $ Var 0)
      $ SimpleConBranches
      $ pure
      ( Builtin.Closure
      , SimpleTelescope $ Vector.cons (mempty, Simple.Scope $ Lit 1)
                        $ Vector.cons (mempty, Simple.Scope $ Lit 1) clArgs
      , Simple.Scope $ Call (vacuous f) (fArgs1 <> fArgs2)
      )
      where
        unknownSize = Sized $ Global "ClosureConvert.UnknownSize"
        clArgs = fmap (vacuous . Simple.mapBound (+ 2)) <$> Vector.take numArgs (unSimpleTelescope tele)
        fArgs1 = Vector.zipWith
          Sized (Var . B <$> Vector.enumFromN 2 (Vector.length clArgs))
                (fmap (unvar F absurd) . Simple.unscope . snd <$> clArgs)
        fArgs2 = Vector.zipWith Sized
          (Var . F <$> Vector.enumFromN 1 numXs)
          (Var . F <$> Vector.enumFromN (fromIntegral $ 1 + numXs) numXs)
        xs = Vector.drop numArgs $ simpleTeleNames tele
        numXs = Vector.length xs
        tele'
          = SimpleTelescope
          $ Vector.cons (nameHint "x_this", Simple.Scope $ Lit 1)
          $ (\h -> (h, Simple.Scope $ Lit 1)) <$> xs
          <|> (\(n, h) -> (h, Simple.Scope $ Var $ B $ Tele $ 1 + n)) <$> Vector.indexed xs
        fReturnSize = unvar id absurd <$> sizeOf functionBody
        returnSize
          = Case (unknownSize $ Call (Global Builtin.DerefName) $ pure $ sized 1 $ Var 0)
          $ SimpleConBranches
          $ pure
          ( Builtin.Closure
          , SimpleTelescope $ Vector.cons (mempty, Simple.Scope $ Lit 1)
                            $ Vector.cons (mempty, Simple.Scope $ Lit 1) clArgs
          , Simple.Scope $ fmap go fReturnSize
          )
        go n | unTele n < numArgs = B $ n + 2 -- from closure
             | otherwise = F $ n + fromIntegral (arity - numArgs) + 1 -- From function args

addSizes :: Vector (Expr v) -> Expr v
addSizes = Vector.foldr1 go
  where
    go x y
      = Call (Global Builtin.AddSizeName)
      $ Vector.cons (Sized (Lit 1) x)
      $ pure $ Sized (Lit 1) y

convertSBody :: SExprM s -> TCM s (SExprM s)
convertSBody (Sized sz e) = Sized <$> convertExpr sz <*> convertBody e

convertSExpr :: SExprM s -> TCM s (SExprM s)
convertSExpr (Sized sz e) = Sized <$> convertExpr sz <*> convertExpr e

convertBranches :: BrsM s -> TCM s (BrsM s)
convertBranches (SimpleConBranches cbrs) = fmap SimpleConBranches $
  forM cbrs $ \(qc, tele, brScope) -> mdo
    tele' <- forMSimpleTele tele $ \h s -> do
      let e = instantiateVar ((vs Vector.!) . unTele) s
      v <- forall_ h e
      e' <- convertExpr e
      return (v, e')
    let vs = fst <$> tele'
        brExpr = instantiateVar ((vs Vector.!) . unTele) brScope
        abstr = teleAbstraction vs
        tele'' = SimpleTelescope $ bimap metaHint (Simple.abstract abstr) <$> tele'
    brExpr' <- convertExpr brExpr
    let brScope' = Simple.abstract abstr brExpr'
    return (qc, tele'', brScope')
convertBranches (SimpleLitBranches lbrs def) = SimpleLitBranches
  <$> mapM (\(l, e) -> (,) l <$> convertExpr e) lbrs <*> convertExpr def
