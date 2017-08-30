{-# LANGUAGE OverloadedStrings #-}
module Backend.ClosureConvert where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import qualified Data.HashMap.Lazy as HashMap
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import qualified Builtin as Builtin
import qualified Builtin.Names as Builtin
import Meta
import Syntax
import qualified Syntax.Sized.Closed as Closed
import qualified Syntax.Sized.Definition as Sized
import qualified Syntax.Sized.Lifted as Lifted
import qualified TypeRep
import Util
import VIX

type Meta = MetaVar Unit

convertDefinitions
  :: [(QName, Sized.Definition Lifted.Expr Void)]
  -> VIX [(QName, Sized.Definition Closed.Expr Void)]
convertDefinitions defs = do
  funSigs <- forM defs $ \(name, def) -> case def of
    Sized.FunctionDef _ _ (Sized.Function tele scope) -> do
      vs <- forMTele tele $ \h () _ ->
        forall h Unit

      es <- forMTele tele $ \_ () s ->
        convertExpr $ instantiateTele pure vs $ vacuous s

      let expr = instantiateTele pure vs $ vacuous scope

      convertedType <- case expr of
        Lifted.Anno _ t -> convertExpr t
        _ -> error "convertDefinitions"

      let abstr = teleAbstraction vs
          tele' = error "convertDefinitions"
            <$> Telescope (Vector.zipWith (\v e -> TeleArg (metaHint v) () (abstract abstr e)) vs es)
          typeScope = error "convertDefinitions"
            <$> abstract abstr convertedType
      return $ Just (name, (tele', typeScope))
    Sized.ConstantDef _ (Sized.Constant (Lifted.Anno (Lifted.Global glob) _)) -> do
      msig <- convertedSignature glob
      return $ (,) name <$> msig
    _ -> return Nothing

  addConvertedSignatures $ HashMap.fromList $ catMaybes funSigs

  forM defs $ \(name, def) -> do
    def' <- convertDefinition def
    return (name, def')

convertDefinition
  :: Sized.Definition Lifted.Expr Void
  -> VIX (Sized.Definition Closed.Expr Void)
convertDefinition (Sized.FunctionDef vis cl (Sized.Function tele scope)) = do
  vs <- forMTele tele $ \h () _ ->
    forall h Unit

  es <- forMTele tele $ \_ () s ->
    convertExpr $ instantiateTele pure vs $ vacuous s

  let expr = instantiateTele pure vs $ vacuous scope
      abstr = teleAbstraction vs
      tele'' = error "convertFunction" <$> Telescope (Vector.zipWith (\v e -> TeleArg (metaHint v) () (abstract abstr e)) vs es)
  expr' <- convertExpr expr
  let scope' = abstract abstr expr'
  return
    $ Sized.FunctionDef vis cl
    $ Sized.Function tele''
    $ error "convertDefinition Function" <$> scope'
convertDefinition (Sized.ConstantDef vis (Sized.Constant expr@(Lifted.Anno (Lifted.Global glob) sz))) = do
  msig <- convertedSignature glob
  expr' <- case msig of
    Nothing -> convertExpr $ vacuous expr
    Just _ -> do
      sz' <- convertExpr $ vacuous sz
      return $ Closed.Anno (Closed.Global glob) sz'
  return
    $ Sized.ConstantDef vis
    $ Sized.Constant
    $ error "convertDefinition Constant" <$> expr'
convertDefinition (Sized.ConstantDef vis (Sized.Constant expr)) = do
  expr' <- convertExpr $ vacuous expr
  return
    $ Sized.ConstantDef vis
    $ Sized.Constant
    $ error "convertDefinition Constant" <$> expr'
convertDefinition Sized.AliasDef = return $ Sized.AliasDef

convertExpr :: Lifted.Expr Meta -> VIX (Closed.Expr Meta)
convertExpr expr = case expr of
  Lifted.Var v -> return $ Closed.Var v
  Lifted.Global g -> do
    msig <- convertedSignature g
    case msig of
      Nothing -> return $ Closed.Global g
      Just sig -> knownCall g sig mempty
  Lifted.Lit l -> return $ Closed.Lit l
  Lifted.Con qc es -> Closed.Con qc <$> mapM convertExpr es
  Lifted.Call (Lifted.Global g) es -> do
    es' <- mapM convertExpr es
    msig <- convertedSignature g
    case msig of
      Nothing -> unknownCall (Closed.Global g) es'
      Just sig -> knownCall g sig es'
  Lifted.Call e es -> do
    e' <- convertExpr e
    es' <- mapM convertExpr es
    unknownCall e' es'
  Lifted.PrimCall retDir e es -> do
    e' <- convertExpr e
    es' <- mapM (traverse convertExpr) es
    return $ Closed.PrimCall retDir e' es'
  Lifted.Let h e bodyScope -> do
    e' <- convertExpr e
    v <- forall h Unit
    let bodyExpr = Util.instantiate1 (pure v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    let bodyScope' = abstract1 v bodyExpr'
    return $ Closed.Let h e' bodyScope'
  Lifted.Case e brs -> Closed.Case <$> convertExpr e <*> convertBranches brs
  Lifted.ExternCode c -> Closed.ExternCode <$> mapM convertExpr c
  Lifted.Anno e t -> Closed.Anno <$> convertExpr e <*> convertExpr t

unknownCall
  :: Closed.Expr Meta
  -> Vector (Closed.Expr Meta)
  -> VIX (Closed.Expr Meta)
unknownCall e es = do
  ptrRep <- gets (Closed.Lit . TypeRep . TypeRep.ptr . vixTarget)
  intRep <- gets (Closed.Lit . TypeRep . TypeRep.int . vixTarget)
  return
    $ Closed.Call (global $ Builtin.applyName $ Vector.length es)
    $ Vector.cons (Closed.Sized ptrRep e)
    $ (Closed.Sized intRep . Closed.typeOf <$> es) <|> es

knownCall
  :: QName
  -> Closed.FunSignature
  -> Vector (Closed.Expr Meta)
  -> VIX (Closed.Expr Meta)
knownCall f (tele, returnTypeScope) args
  | numArgs < arity = do
    vs <- forM fArgs $ \_ -> forall mempty Unit
    target <- gets vixTarget
    let intRep, ptrRep :: Closed.Expr v
        intRep = Closed.Lit $ TypeRep $ TypeRep.int target
        ptrRep = Closed.Lit $ TypeRep $ TypeRep.ptr target
    let returnType = instantiateTele pure vs $ vacuous returnTypeScope
        go v | i < Vector.length fArgs1 = B $ Tele $ 2 + i
             | otherwise = F $ Tele $ 1 + numXs - numArgs + i
          where
            i = fromMaybe (error "knownCall elemIndex") $ Vector.elemIndex v vs
    let tele' = Telescope
          $ Vector.cons (TeleArg "x_this" () $ Scope ptrRep)
          $ (\h -> TeleArg h () $ Scope intRep) <$> xs
          <|> (\(n, h) -> TeleArg h () $ Scope $ pure $ B $ 1 + Tele n) <$> Vector.indexed xs
    let fNumArgs = Closed.Lams tele'
          $ toScope
          $ fmap B
          $ Closed.Case (Builtin.deref target $ Closed.Var 0)
          $ ConBranches
          $ pure
          $ ConBranch
            Builtin.Closure
            (Telescope $ Vector.cons (TeleArg mempty () $ Scope intRep)
                       $ Vector.cons (TeleArg mempty () $ Scope intRep) clArgs')
            (toScope
            $ Closed.Sized (go <$> returnType)
            $ Closed.Call (global f) fArgs)
    return
      $ Closed.Con Builtin.Ref
      $ pure
      $ Builtin.sizedCon (Closed.Lit $ TypeRep TypeRep.Unit) Builtin.Closure
      $ Vector.cons (Closed.Sized ptrRep fNumArgs)
      $ Vector.cons (Closed.Sized intRep $ Closed.Lit $ Integer $ fromIntegral $ arity - numArgs) args
  | numArgs == arity
    = return $ Closed.Call (global f) args
  | otherwise = do
    let (knownArgs, unknownArgs) = Vector.splitAt arity args
    unknownCall (Closed.Call (global f) knownArgs) unknownArgs
  where
    numArgs = Vector.length args
    arity = teleLength tele
    clArgs = (\(TeleArg h d s) -> TeleArg h d $ mapBound (+ 2) s) <$> Vector.take numArgs (unTelescope tele)
    clArgs' = (\(TeleArg h _ s) -> TeleArg h () $ vacuous s) <$> clArgs
    fArgs1 = Vector.zipWith Closed.Anno
      (Closed.Var . B <$> Vector.enumFromN 2 numArgs)
      ((\(TeleArg _ _ s) -> unvar F absurd <$> fromScope s) <$> clArgs)
    fArgs2 = Vector.zipWith Closed.Anno
      (Closed.Var . F <$> Vector.enumFromN (fromIntegral $ 1 + numXs) numXs)
      (Closed.Var . F <$> Vector.enumFromN 1 numXs)
    xs = Vector.drop numArgs $ teleNames tele
    numXs = Vector.length xs
    fArgs = fArgs1 <> fArgs2

convertBranches
  :: Branches QConstr () Lifted.Expr Meta
  -> VIX (Branches QConstr () Closed.Expr Meta)
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forMTele tele $ \h () _ ->
      forall h Unit
    es <- forMTele tele $ \_ () s ->
      convertExpr $ instantiateTele pure vs s
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ Vector.zipWith (\v e -> TeleArg (metaHint v) () $ abstract abstr e) vs es
    brExpr' <- convertExpr brExpr
    let brScope' = abstract abstr brExpr'
    return $ ConBranch qc tele'' brScope'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
