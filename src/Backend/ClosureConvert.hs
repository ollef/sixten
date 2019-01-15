{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Backend.ClosureConvert where

import Protolude hiding (typeRep, Type)

import qualified Data.HashSet as HashSet
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Rock

import Backend.Lift(runLift, liftThing, Lift)
import qualified Builtin
import qualified Builtin.Names as Builtin
import Driver.Query
import Effect.Context as Context
import FreeVar
import Syntax
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import Syntax.Sized.Lifted
import qualified TypeRep
import Util
import VIX

type ClosureConvert = Lift () (Closed (Sized.Definition Expr))
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
    teleMapExtendContext tele (pure . const ()) $ \vs -> do
      es <- forMTele tele $ \_ _ s ->
        convertExpr $ instantiateTele pure vs s

      let t = instantiateTele pure vs tscope
      convertedType <- convertExpr t

      tele' <- varTelescope (Vector.zip vs es)

      let closedTele' = close (panic "convertDefinitions") tele'
          typeScope = close (panic "convertDefinitions") $ abstract (teleAbstraction vs) convertedType
      return $ Just (closedTele', typeScope)
  Sized.ConstantDef _ (Sized.Constant (Anno (Global glob) _)) ->
    fetch $ ConvertedSignature glob
  _ -> return Nothing

convertDefinition
  :: GName
  -> Closed (Sized.Definition Expr)
  -> ClosureConvert (Closed (Sized.Definition Expr))
convertDefinition name (Closed (Sized.FunctionDef vis cl (Sized.Function tele scope@(AnnoScope exprScope _)))) =
  teleMapExtendContext tele (pure . const ()) $ \vs -> do
    msig <- fetch $ ConvertedSignature name
    case msig of
      Nothing -> do
        es <- forMTele tele $ \_ _ s ->
          convertExpr $ instantiateTele pure vs s

        let annoExpr = instantiateAnnoTele pure vs scope
        annoExpr' <- convertAnnoExpr annoExpr
        fun <- Sized.function (Vector.zip vs es) annoExpr'
        return
          $ close (panic "convertDefinition Function")
          $ Sized.FunctionDef vis cl fun
      Just (tele', typeScope) -> do
        let es = forTele (open tele') $ \_ _ s ->
              instantiateTele pure vs s

        let expr = instantiateTele pure vs exprScope
            type' = instantiateTele pure vs $ open typeScope
        expr' <- convertExpr expr
        let annoExpr' = Anno expr' type'
        fun <- Sized.function (Vector.zip vs es) annoExpr'
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

convertAnnoExpr :: Anno Expr FreeVar -> ClosureConvert (Anno Expr FreeVar)
convertAnnoExpr (Anno expr typ) = Anno <$> convertExpr expr <*> convertExpr typ

convertExpr :: Expr FreeVar -> ClosureConvert (Expr FreeVar)
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
    e' <- convertAnnoExpr e
    Context.freshExtend h Explicit () $ \v -> do
      let bodyExpr = Util.instantiate1 (pure v) bodyScope
      bodyExpr' <- convertExpr bodyExpr
      let_ v e' bodyExpr'
  Case e brs -> Case <$> convertAnnoExpr e <*> convertBranches brs
  ExternCode c retType -> ExternCode <$> mapM convertAnnoExpr c <*> convertExpr retType

unknownCall
  :: Expr FreeVar
  -> Vector (Anno Expr FreeVar)
  -> ClosureConvert (Expr FreeVar)
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
  -> Vector (Anno Expr FreeVar)
  -> ClosureConvert (Expr FreeVar)
knownCall f (Closed tele, Closed returnTypeScope) args
  | numArgs < arity = do
    target <- fetch Target
    piRep <- Lit . TypeRep <$> fetchPiRep
    intRep <- Lit . TypeRep <$> fetchIntRep
    fNumArgs <- liftClosureFun f (close identity tele, close identity returnTypeScope) numArgs
    return
      $ Con Builtin.Ref
      $ pure
      $ Builtin.sizedCon target (MkType TypeRep.UnitRep) Builtin.Closure
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
liftClosureFun f (Closed tele, Closed returnTypeScope) numCaptured = do
  vs <- forTeleWithPrefixM tele $ \h p s vs -> do
    v <- freeVar h p ()
    return (v, instantiateTele pure (fst <$> vs) s)

  typeRep <- MkType <$> fetchTypeRep
  ptrRep <- MkType <$> fetchPtrRep
  piRep <- MkType <$> fetchPiRep
  intRep <- MkType <$> fetchIntRep

  let (capturedArgs, remainingParams) = Vector.splitAt numCaptured vs
  this <- freeVar "this" Explicit ()
  typeParams <- forM remainingParams $ \(v, _) -> do
    v' <- freeVar (varHint v) (varPlicitness v) ()
    return (v', typeRep)
  let remainingParams'
        = flip fmap (Vector.zip remainingParams typeParams)
        $ \((v, _), (tv, _)) -> (v, pure tv)

  let funParams = pure (this, ptrRep) <> typeParams <> remainingParams'

  unused1 <- freeVar "unused" Explicit ()
  unused2 <- freeVar "unused" Explicit ()
  let clArgs
        = Vector.cons (unused1, piRep)
        $ Vector.cons (unused2, intRep)
        capturedArgs
      funArgs = capturedArgs <> remainingParams'
      funArgs' = flip fmap funArgs $ \(v, t) -> Anno (pure v) t

      returnType = instantiateTele pure (fst <$> vs) returnTypeScope
      returnTypeVars = toHashSet returnType
      fReturnType
        | any (`HashSet.member` returnTypeVars) $ fst <$> capturedArgs =
          Case (Anno (Builtin.deref $ pure this) (Global $ gname "ClosureConvert.knownCall.unknownSize"))
          $ ConBranches $ pure $ typedConBranch Builtin.Closure clArgs returnType
        | otherwise = returnType

  liftThing
    $ close (panic "liftClosureFun")
    $ Sized.FunctionDef Private Sized.IsClosure
    $ Sized.function funParams
    $ Anno
      (Case (Anno (Builtin.deref $ pure this) (Global $ gname "ClosureConvert.knownCall.unknownSize"))
      $ ConBranches $ pure $ typedConBranch Builtin.Closure clArgs
      $ Call (global f) funArgs')
      fReturnType

convertBranches
  :: Branches Expr FreeVar
  -> ClosureConvert (Branches Expr FreeVar)
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forMTele tele $ \h p _ ->
      freeVar h p ()
    es <- forMTele tele $ \_ _ s ->
      convertExpr $ instantiateTele pure vs s
    let brExpr = instantiateTele pure vs brScope
    brExpr' <- convertExpr brExpr
    return $ typedConBranch qc (Vector.zip vs es) brExpr'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
