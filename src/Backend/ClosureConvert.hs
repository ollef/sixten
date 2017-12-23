{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Backend.ClosureConvert where

import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import Data.Maybe
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Backend.Lift(runLift, liftThing, Lift)
import qualified Builtin
import qualified Builtin.Names as Builtin
import FreeVar
import Syntax
import qualified Syntax.Sized.Definition as Sized
import Syntax.Sized.Lifted
import qualified TypeRep
import Util
import VIX

type FV = FreeVar ()
type ClosureConvert = Lift (Sized.Function Expr Void) VIX

convertDefinitions
  :: [(QName, Sized.Definition Expr Void)]
  -> VIX [[(QName, Sized.Definition Expr Void)]]
convertDefinitions [] = return []
convertDefinitions ds@((QName mname name, _):_) = do
  (ds', fs) <- runLift (QName mname $ name <> "-converted") (convertDefinitionsM ds)
  return
    $ Sized.dependencyOrder
    $ ds' <|> second (Sized.FunctionDef Private Sized.IsClosure) <$> fs

convertDefinitionsM
  :: [(QName, Sized.Definition Expr Void)]
  -> ClosureConvert [(QName, Sized.Definition Expr Void)]
convertDefinitionsM defs = do
  funSigs <- forM defs $ \(name, def) -> case def of
    Sized.FunctionDef _ _ (Sized.Function tele scope) -> do
      vs <- lift $ forMTele tele $ \h () _ ->
        freeVar h ()

      es <- forMTele tele $ \_ () s ->
        convertExpr $ instantiateTele pure vs $ vacuous s

      let expr = instantiateTele pure vs $ vacuous scope

      convertedType <- case expr of
        Anno _ t -> convertExpr t
        _ -> error "convertDefinitions"

      let abstr = teleAbstraction vs
          tele' = error "convertDefinitions"
            <$> Telescope (Vector.zipWith (\v e -> TeleArg (varHint v) () (abstract abstr e)) vs es)
          typeScope = error "convertDefinitions"
            <$> abstract abstr convertedType
      return $ Just (name, (tele', typeScope))
    Sized.ConstantDef _ (Sized.Constant (Anno (Global glob) _)) -> do
      msig <- lift $ convertedSignature glob
      return $ (,) name <$> msig
    _ -> return Nothing

  lift $ addConvertedSignatures $ HashMap.fromList $ catMaybes funSigs

  forM defs $ \(name, def) -> do
    def' <- convertDefinition def
    return (name, def')

convertDefinition
  :: Sized.Definition Expr Void
  -> ClosureConvert (Sized.Definition Expr Void)
convertDefinition (Sized.FunctionDef vis cl (Sized.Function tele scope)) = do
  vs <- lift $ forMTele tele $ \h () _ ->
    freeVar h ()

  es <- forMTele tele $ \_ () s ->
    convertExpr $ instantiateTele pure vs $ vacuous s

  let expr = instantiateTele pure vs $ vacuous scope
      abstr = teleAbstraction vs
      tele'' = error "convertFunction" <$> Telescope (Vector.zipWith (\v e -> TeleArg (varHint v) () (abstract abstr e)) vs es)
  expr' <- convertExpr expr
  let scope' = abstract abstr expr'
  return
    $ Sized.FunctionDef vis cl
    $ Sized.Function tele''
    $ error "convertDefinition Function" <$> scope'
convertDefinition (Sized.ConstantDef vis (Sized.Constant expr@(Anno (Global glob) sz))) = do
  msig <- lift $ convertedSignature glob
  expr' <- case msig of
    Nothing -> convertExpr $ vacuous expr
    Just _ -> do
      sz' <- convertExpr $ vacuous sz
      return $ Anno (Global glob) sz'
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
convertDefinition Sized.AliasDef = return Sized.AliasDef

convertExpr :: Expr FV -> ClosureConvert (Expr FV)
convertExpr expr = case expr of
  Var v -> return $ Var v
  Global g -> do
    msig <- lift $ convertedSignature g
    case msig of
      Nothing -> return $ Global g
      Just sig -> knownCall g sig mempty
  Lit l -> return $ Lit l
  Con qc es -> Con qc <$> mapM convertExpr es
  (callsView -> Just (Global g, es)) -> do
    es' <- mapM convertExpr es
    msig <- lift $ convertedSignature g
    case msig of
      Nothing -> unknownCall (Global g) es'
      Just sig -> knownCall g sig es'
  (callsView -> Just (e, es)) -> do
    e' <- convertExpr e
    es' <- mapM convertExpr es
    unknownCall e' es'
  Call {} -> error "convertExpr Call"
  PrimCall retDir e es -> do
    e' <- convertExpr e
    es' <- mapM (traverse convertExpr) es
    return $ PrimCall retDir e' es'
  Let h e t bodyScope -> do
    e' <- convertExpr e
    t' <- convertExpr t
    v <- lift $ freeVar h ()
    let bodyExpr = Util.instantiate1 (pure v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    let bodyScope' = abstract1 v bodyExpr'
    return $ Let h e' t' bodyScope'
  Case e brs -> Case <$> convertExpr e <*> convertBranches brs
  ExternCode c -> ExternCode <$> mapM convertExpr c
  Anno e t -> Anno <$> convertExpr e <*> convertExpr t

unknownCall
  :: Expr FV
  -> Vector (Expr FV)
  -> ClosureConvert (Expr FV)
unknownCall e es = do
  ptrRep <- MkType <$> getPtrRep
  intRep <- MkType <$> getIntRep
  return
    $ Call (global $ Builtin.applyName $ Vector.length es)
    $ Vector.cons (Sized ptrRep e)
    $ (Sized intRep . typeOf <$> es) <|> es

knownCall
  :: QName
  -> FunSignature
  -> Vector (Expr FV)
  -> ClosureConvert (Expr FV)
knownCall f (tele, returnTypeScope) args
  | numArgs < arity = do
    vs <- forM (teleNames tele) $ \h -> freeVar h ()
    target <- getTarget
    let intRep, ptrRep :: Expr v
        intRep = MkType $ TypeRep.intRep target
        ptrRep = MkType $ TypeRep.ptrRep target
    let returnType = instantiateTele pure vs $ vacuous returnTypeScope
        varIndex = hashedElemIndex vs
        go v | i < Vector.length fArgs1 = B $ TeleVar $ 2 + i
             | otherwise = F $ TeleVar $ 1 + numXs - numArgs + i
          where
            i = fromMaybe (error "knownCall elemIndex") $ varIndex v
    let tele' = Telescope
          $ Vector.cons (TeleArg "x_this" () $ Scope ptrRep)
          $ (\h -> TeleArg h () $ Scope intRep) <$> xs
          <|> (\(n, h) -> TeleArg h () $ Scope $ pure $ B $ 1 + TeleVar n) <$> Vector.indexed xs
    fNumArgs <- liftThing
      $ Sized.Function tele'
      $ toScope
      $ fmap B
      $ Case (Builtin.deref target $ Var 0)
      $ ConBranches
      $ pure
      $ ConBranch
        Builtin.Closure
        (Telescope $ Vector.cons (TeleArg mempty () $ Scope ptrRep)
                   $ Vector.cons (TeleArg mempty () $ Scope intRep) clArgs')
        (toScope
        $ Sized (go <$> returnType)
        $ Call (global f) fArgs)
    return
      $ Con Builtin.Ref
      $ pure
      $ Builtin.sizedCon target (MkType TypeRep.UnitRep) Builtin.Closure
      $ Vector.cons (Sized ptrRep $ global fNumArgs)
      $ Vector.cons (Sized intRep $ Lit $ Integer $ fromIntegral $ arity - numArgs) args
  | numArgs == arity
    = return $ Call (global f) args
  | otherwise = do
    let (knownArgs, unknownArgs) = Vector.splitAt arity args
    unknownCall (Call (global f) knownArgs) unknownArgs
  where
    numArgs = Vector.length args
    arity = teleLength tele
    clArgs = (\(TeleArg h d s) -> TeleArg h d $ mapBound (+ 2) s) <$> Vector.take numArgs (unTelescope tele)
    clArgs' = (\(TeleArg h _ s) -> TeleArg h () $ vacuous s) <$> clArgs
    fArgs1 = Vector.zipWith Anno
      (Var . B <$> Vector.enumFromN 2 numArgs)
      ((\(TeleArg _ _ s) -> fromScope s) <$> clArgs')
    fArgs2 = Vector.zipWith Anno
      (Var . F <$> Vector.enumFromN (fromIntegral $ 1 + numXs) numXs)
      (Var . F <$> Vector.enumFromN 1 numXs)
    xs = Vector.drop numArgs $ teleNames tele
    numXs = Vector.length xs
    fArgs = fArgs1 <> fArgs2

convertBranches
  :: Branches QConstr () Expr FV
  -> ClosureConvert (Branches QConstr () Expr FV)
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- lift $ forMTele tele $ \h () _ ->
      freeVar h ()
    es <- forMTele tele $ \_ () s ->
      convertExpr $ instantiateTele pure vs s
    let brExpr = instantiateTele pure vs brScope
        abstr = teleAbstraction vs
        tele'' = Telescope $ Vector.zipWith (\v e -> TeleArg (varHint v) () $ abstract abstr e) vs es
    brExpr' <- convertExpr brExpr
    let brScope' = abstract abstr brExpr'
    return $ ConBranch qc tele'' brScope'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
