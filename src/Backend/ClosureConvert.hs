{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Backend.ClosureConvert where

import Protolude hiding (typeRep, Type)

import qualified Data.HashSet as HashSet
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Rock

import Backend.Lift(runLift, liftThing, Lift)
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect
import qualified Effect.Context as Context
import Syntax
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import Syntax.Sized.Lifted
import Util
import VIX

type ClosureConvert = Lift (Closed (Sized.Definition Expr))
type ConvertedSignature = (Closed (Telescope Type), Closed (Scope TeleVar Type))

runConvertDefinition
  :: GName
  -> Closed (Sized.Definition Expr)
  -> VIX [(GName, Closed (Sized.Definition Expr))]
runConvertDefinition name def = do
  (def', fs) <- runLift name "converted" (convertDefinition name def)
  return ((name, def') : fs)

runConvertedSignature
  :: GName
  -> Closed (Sized.Definition Expr)
  -> VIX (Maybe ConvertedSignature, [(GName, Closed (Sized.Definition Expr))])
runConvertedSignature name def = runLift name "converted-sig" (convertSignature def)

convertSignature
  :: Closed (Sized.Definition Expr)
  -> ClosureConvert (Maybe ConvertedSignature)
convertSignature def = case open def of
  Sized.FunctionDef _ _ (Sized.Function tele (AnnoScope _ tscope)) ->
    teleMapExtendContext tele convertExpr $ \vs -> do
      let
        t = instantiateTele pure vs tscope
      convertedType <- convertExpr t
      tele' <- varTelescope vs
      let
        closedTele' = close (panic "convertDefinitions") tele'
        typeScope = close (panic "convertDefinitions") $ abstract (teleAbstraction vs) convertedType
      return $ Just (closedTele', typeScope)
  Sized.ConstantDef _ (Sized.Constant (Anno (Global glob) _)) ->
    fetch $ ConvertedSignature glob
  _ -> return Nothing

convertDefinition
  :: GName
  -> Closed (Sized.Definition Expr)
  -> ClosureConvert (Closed (Sized.Definition Expr))
convertDefinition name (Closed (Sized.FunctionDef vis cl (Sized.Function tele scope@(AnnoScope exprScope _)))) = do
  msig <- fetch $ ConvertedSignature name
  case msig of
    Nothing ->
      teleMapExtendContext tele convertExpr $ \vs -> do
        let
          annoExpr = instantiateAnnoTele pure vs scope
        annoExpr' <- convertAnnoExpr annoExpr
        fun <- Sized.function vs annoExpr'
        return
          $ close (panic "convertDefinition Function")
          $ Sized.FunctionDef vis cl fun
    Just (Closed tele', typeScope) ->
      teleExtendContext tele' $ \vs -> do
        let
          expr = instantiateTele pure vs exprScope
          type' = instantiateTele pure vs $ open typeScope
        expr' <- convertExpr expr
        let annoExpr' = Anno expr' type'
        fun <- Sized.function vs annoExpr'
        return
          $ close (panic "convertDefinition Function")
          $ Sized.FunctionDef vis cl fun
convertDefinition _ (Closed (Sized.ConstantDef vis (Sized.Constant expr@(Anno (Global glob) sz)))) = do
  msig <- fetch $ ConvertedSignature glob
  expr' <- case msig of
    Nothing -> convertAnnoExpr expr
    Just _ -> do
      sz' <- convertExpr sz
      return $ Anno (Global glob) sz'
  return
    $ close (panic "convertDefinition Constant")
    $ Sized.ConstantDef vis
    $ Sized.Constant expr'
convertDefinition _ (Closed (Sized.ConstantDef vis (Sized.Constant expr))) = do
  expr' <- convertAnnoExpr expr
  return
    $ close (panic "convertDefinition Constant")
    $ Sized.ConstantDef vis
    $ Sized.Constant expr'
convertDefinition _ (Closed Sized.AliasDef) = return $ close identity Sized.AliasDef

convertAnnoExpr :: Anno Expr Var -> ClosureConvert (Anno Expr Var)
convertAnnoExpr (Anno expr typ) = Anno <$> convertExpr expr <*> convertExpr typ

convertExpr :: Expr Var -> ClosureConvert (Expr Var)
convertExpr expr = case expr of
  Var v -> return $ Var v
  Global g -> do
    msig <- fetch $ ConvertedSignature g
    case msig of
      Nothing -> return $ Global g
      Just sig -> knownCall g sig mempty
  Lit l -> return $ Lit l
  Con qc es -> Con qc <$> mapM convertAnnoExpr es
  (callsView -> Just (Global g, es)) -> do
    es' <- mapM convertAnnoExpr es
    msig <- fetch $ ConvertedSignature g
    case msig of
      Nothing -> unknownCall (Global g) es'
      Just sig -> knownCall g sig es'
  (callsView -> Just (e, es)) -> do
    e' <- convertExpr e
    es' <- mapM convertAnnoExpr es
    unknownCall e' es'
  Call {} -> panic "convertExpr Call"
  PrimCall retDir e es -> do
    e' <- convertExpr e
    es' <- mapM (traverse convertAnnoExpr) es
    return $ PrimCall retDir e' es'
  Let h e bodyScope -> do
    Anno e' t' <- convertAnnoExpr e
    Context.freshExtend (binding h Explicit t') $ \v -> do
      let bodyExpr = Util.instantiate1 (pure v) bodyScope
      bodyExpr' <- convertExpr bodyExpr
      let_ v e' bodyExpr'
  Case e brs -> Case <$> convertAnnoExpr e <*> convertBranches brs
  ExternCode c retType -> ExternCode <$> mapM convertAnnoExpr c <*> convertExpr retType

unknownCall
  :: Expr Var
  -> Vector (Anno Expr Var)
  -> ClosureConvert (Expr Var)
unknownCall e es = do
  ptrRep <- MkType <$> fetchPtrRep
  intRep <- MkType <$> fetchIntRep
  return
    $ Call (global $ gname $ Builtin.applyName $ Vector.length es)
    $ Vector.cons (Anno e ptrRep)
    $ (flip Anno intRep . typeAnno <$> es) <|> es

knownCall
  :: GName
  -> FunSignature
  -> Vector (Anno Expr Var)
  -> ClosureConvert (Expr Var)
knownCall f (Closed tele, Closed returnTypeScope) args
  | numArgs < arity = do
    piRep <- Lit . TypeRep <$> fetchPiRep
    intRep <- Lit . TypeRep <$> fetchIntRep
    fNumArgs <- liftClosureFun f (close identity tele, close identity returnTypeScope) numArgs
    return
      $ Con Builtin.Closure
      $ Vector.cons (Anno (global fNumArgs) piRep)
      $ Vector.cons (Anno (Lit $ Integer $ fromIntegral $ arity - numArgs) intRep) args
  | numArgs == arity
    = return $ Call (global f) args
  | otherwise = do
    let (knownArgs, unknownArgs) = Vector.splitAt arity args
    unknownCall (Call (global f) knownArgs) unknownArgs
  where
    numArgs = Vector.length args
    arity = teleLength tele

liftClosureFun
  :: GName
  -> FunSignature
  -> Int
  -> ClosureConvert GName
liftClosureFun f (Closed tele, Closed returnTypeScope) numCaptured =
  teleExtendContext tele $ \vs -> do
    context <- getContext
    typeRep <- MkType <$> fetchTypeRep
    ptrRep <- MkType <$> fetchPtrRep
    piRep <- MkType <$> fetchPiRep
    intRep <- MkType <$> fetchIntRep

    let
      (capturedArgs, remainingParams) = Vector.splitAt numCaptured vs
      typedCapturedArgs = (\v -> (v, Context.lookupType v context)) <$> capturedArgs

    Context.freshExtend (binding "this" Explicit ptrRep) $ \this -> do
      remainingTele <- varTelescope remainingParams
      teleMapExtendContext remainingTele (pure . const typeRep) $ \typeParams -> do
        let
          remainingParams' = Vector.zip remainingParams $ pure <$> typeParams
          funParams = pure (this, ptrRep) <> ((, typeRep) <$> typeParams) <> remainingParams'

        Context.freshExtend (binding "unused" Explicit piRep) $ \unused1 ->
          Context.freshExtend (binding "unused" Explicit intRep) $ \unused2 -> do
            let
              clArgs
                = Vector.cons unused1
                $ Vector.cons unused2
                capturedArgs
              funArgs = typedCapturedArgs <> remainingParams'
              funArgs' = foreach funArgs $ \(v, t) -> Anno (pure v) t

              returnType = instantiateTele pure vs returnTypeScope
              returnTypeVars = toHashSet returnType

            fReturnType <-
              if any (`HashSet.member` returnTypeVars) capturedArgs then do
                br <- conBranch Builtin.Closure clArgs returnType
                return $ Case (Anno (pure this) (Global $ gname "ClosureConvert.knownCall.unknownSize"))
                  $ ConBranches $ pure br
              else
                return returnType

            br <- conBranch Builtin.Closure clArgs $ Call (global f) funArgs'

            fun <- Sized.typedFunction
              funParams
              $ Anno
                (Case (Anno (pure this) (Global $ gname "ClosureConvert.knownCall.unknownSize"))
                  $ ConBranches $ pure br)
                fReturnType
            liftThing
              $ close (panic "liftClosureFun")
              $ Sized.FunctionDef Private Sized.IsClosure fun

convertBranches
  :: Branches Expr Var
  -> ClosureConvert (Branches Expr Var)
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) ->
    teleMapExtendContext tele convertExpr $ \vs -> do
    let brExpr = instantiateTele pure vs brScope
    brExpr' <- convertExpr brExpr
    conBranch qc vs brExpr'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
