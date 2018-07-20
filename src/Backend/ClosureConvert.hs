{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Backend.ClosureConvert where

import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
import Data.Maybe
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import Backend.Lift(runLift, liftThing, Lift)
import qualified Builtin
import qualified Builtin.Names as Builtin
import FreeVar
import Syntax
import Syntax.Sized.Anno
import qualified Syntax.Sized.Definition as Sized
import Syntax.Sized.Lifted
import qualified TypeRep
import Util
import VIX

type FV = FreeVar ()
type ClosureConvert = Lift (Closed (Sized.Function Expr)) VIX

convertDefinitions
  :: [(QName, Closed (Sized.Definition Expr))]
  -> VIX [[(QName, Closed (Sized.Definition Expr))]]
convertDefinitions [] = return []
convertDefinitions ds@((QName mname name, _):_) = do
  (ds', fs) <- runLift (QName mname $ name <> "-converted") (convertDefinitionsM ds)
  return
    $ Sized.dependencyOrder
    $ ds' <|> second (mapClosed $ Sized.FunctionDef Private Sized.IsClosure) <$> fs

convertDefinitionsM
  :: [(QName, Closed (Sized.Definition Expr))]
  -> ClosureConvert [(QName, Closed (Sized.Definition Expr))]
convertDefinitionsM defs = do
  funSigs <- forM defs $ \(name, def) -> case open def of
    Sized.FunctionDef _ _ (Sized.Function tele scope) -> do
      vs <- forMTele tele $ \h () _ ->
        freeVar h ()

      es <- forMTele tele $ \_ () s ->
        convertExpr $ instantiateTele pure vs s

      let Anno _ t = instantiateAnnoTele pure vs scope
      convertedType <- convertExpr t

      let tele' = close (error "convertDefinitions") $ varTelescope (Vector.zip vs es)
          typeScope = close (error "convertDefinitions") $ abstract (teleAbstraction vs) convertedType
      return $ Just (name, (tele', typeScope))
    Sized.ConstantDef _ (Sized.Constant (Anno (Global glob) _)) -> do
      msig <- convertedSignature glob
      return $ (,) name <$> msig
    _ -> return Nothing

  addConvertedSignatures $ HashMap.fromList $ catMaybes funSigs

  forM defs $ \(name, def) -> do
    def' <- convertDefinition def
    return (name, def')

convertDefinition
  :: Closed (Sized.Definition Expr)
  -> ClosureConvert (Closed (Sized.Definition Expr))
convertDefinition (Closed (Sized.FunctionDef vis cl (Sized.Function tele scope))) = do
  vs <- forMTele tele $ \h () _ ->
    freeVar h ()

  es <- forMTele tele $ \_ () s ->
    convertExpr $ instantiateTele pure vs s

  let expr = instantiateAnnoTele pure vs scope
  expr' <- convertAnnoExpr expr
  return
    $ close (error "convertDefinition Function")
    $ Sized.FunctionDef vis cl
    $ Sized.function (Vector.zip vs es) expr'
convertDefinition (Closed (Sized.ConstantDef vis (Sized.Constant expr@(Anno (Global glob) sz)))) = do
  msig <- convertedSignature glob
  expr' <- case msig of
    Nothing -> convertAnnoExpr expr
    Just _ -> do
      sz' <- convertExpr sz
      return $ Anno (Global glob) sz'
  return
    $ close (error "convertDefinition Constant")
    $ Sized.ConstantDef vis
    $ Sized.Constant expr'
convertDefinition (Closed (Sized.ConstantDef vis (Sized.Constant expr))) = do
  expr' <- convertAnnoExpr expr
  return
    $ close (error "convertDefinition Constant")
    $ Sized.ConstantDef vis
    $ Sized.Constant expr'
convertDefinition (Closed Sized.AliasDef) = return $ close id Sized.AliasDef

convertAnnoExpr :: Anno Expr FV -> ClosureConvert (Anno Expr FV)
convertAnnoExpr (Anno expr typ) = Anno <$> convertExpr expr <*> convertExpr typ

convertExpr :: Expr FV -> ClosureConvert (Expr FV)
convertExpr expr = case expr of
  Var v -> return $ Var v
  Global g -> do
    msig <- convertedSignature g
    case msig of
      Nothing -> return $ Global g
      Just sig -> knownCall g sig mempty
  Lit l -> return $ Lit l
  Con qc es -> Con qc <$> mapM convertAnnoExpr es
  (callsView -> Just (Global g, es)) -> do
    es' <- mapM convertAnnoExpr es
    msig <- convertedSignature g
    case msig of
      Nothing -> unknownCall (Global g) es'
      Just sig -> knownCall g sig es'
  (callsView -> Just (e, es)) -> do
    e' <- convertExpr e
    es' <- mapM convertAnnoExpr es
    unknownCall e' es'
  Call {} -> error "convertExpr Call"
  PrimCall retDir e es -> do
    e' <- convertExpr e
    es' <- mapM (traverse convertAnnoExpr) es
    return $ PrimCall retDir e' es'
  Let h e bodyScope -> do
    e' <- convertAnnoExpr e
    v <- freeVar h ()
    let bodyExpr = Util.instantiate1 (pure v) bodyScope
    bodyExpr' <- convertExpr bodyExpr
    return $ let_ v e' bodyExpr'
  Case e brs -> Case <$> convertAnnoExpr e <*> convertBranches brs
  ExternCode c retType -> ExternCode <$> mapM convertAnnoExpr c <*> convertExpr retType

unknownCall
  :: Expr FV
  -> Vector (Anno Expr FV)
  -> ClosureConvert (Expr FV)
unknownCall e es = do
  ptrRep <- MkType <$> getPtrRep
  intRep <- MkType <$> getIntRep
  return
    $ Call (global $ Builtin.applyName $ Vector.length es)
    $ Vector.cons (Anno e ptrRep)
    $ (flip Anno intRep . typeAnno <$> es) <|> es

knownCall
  :: QName
  -> FunSignature
  -> Vector (Anno Expr FV)
  -> ClosureConvert (Expr FV)
knownCall f (Closed tele, Closed returnTypeScope) args
  | numArgs < arity = do
    target <- getTarget
    piRep <- Lit . TypeRep <$> getPiRep
    intRep <- Lit . TypeRep <$> getIntRep
    fNumArgs <- liftClosureFun f (close id tele, close id returnTypeScope) numArgs
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
  :: QName
  -> FunSignature
  -> Int
  -> ClosureConvert QName
liftClosureFun f (Closed tele, Closed returnTypeScope) numCaptured = do
  vs <- forTeleWithPrefixM tele $ \h _ s vs -> do
    v <- freeVar h ()
    return (v, instantiateTele pure (fst <$> vs) s)

  typeRep <- MkType <$> getTypeRep
  ptrRep <- MkType <$> getPtrRep
  piRep <- MkType <$> getPiRep
  intRep <- MkType <$> getIntRep

  let (capturedArgs, remainingParams) = Vector.splitAt numCaptured vs
  this <- freeVar "this" ()
  typeParams <- forM remainingParams $ \(v, _) -> do
    v' <- freeVar (varHint v) ()
    return (v', typeRep)
  let remainingParams'
        = flip fmap (Vector.zip remainingParams typeParams)
        $ \((v, _), (tv, _)) -> (v, pure tv)

  let funParams = pure (this, ptrRep) <> typeParams <> remainingParams'

  unused1 <- freeVar "unused" ()
  unused2 <- freeVar "unused" ()
  let clArgs
        = Vector.cons (unused1, piRep)
        $ Vector.cons (unused2, intRep)
        capturedArgs
      funArgs = capturedArgs <> remainingParams'
      funArgs' = flip fmap funArgs $ \(v, t) -> Anno (pure v) t

      returnType = instantiateTele pure (fst <$> vs) returnTypeScope
      fReturnType
        | any (\x -> HashSet.member x $ toHashSet returnType) $ fst <$> capturedArgs =
          Case (Anno (Builtin.deref $ pure this) (Global "ClosureConvert.knownCall.unknownSize"))
          $ ConBranches $ pure $ typedConBranch Builtin.Closure clArgs returnType
        | otherwise = returnType

  liftThing
    $ close (error "liftClosureFun")
    $ Sized.function funParams
    $ Anno
      (Case (Anno (Builtin.deref $ pure this) (Global "ClosureConvert.knownCall.unknownSize"))
      $ ConBranches $ pure $ typedConBranch Builtin.Closure clArgs
      $ Call (global f) funArgs')
      fReturnType

convertBranches
  :: Branches () Expr FV
  -> ClosureConvert (Branches () Expr FV)
convertBranches (ConBranches cbrs) = fmap ConBranches $
  forM cbrs $ \(ConBranch qc tele brScope) -> do
    vs <- forMTele tele $ \h () _ ->
      freeVar h ()
    es <- forMTele tele $ \_ () s ->
      convertExpr $ instantiateTele pure vs s
    let brExpr = instantiateTele pure vs brScope
    brExpr' <- convertExpr brExpr
    return $ typedConBranch qc (Vector.zip vs es) brExpr'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
