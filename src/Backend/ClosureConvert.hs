{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Backend.ClosureConvert where

import Control.Applicative
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.HashSet as HashSet
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
import Syntax.Sized.Anno
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
      vs <- forMTele tele $ \h () _ ->
        freeVar h ()

      es <- forMTele tele $ \_ () s ->
        convertExpr $ instantiateTele pure vs $ vacuous s

      let Anno _ t = instantiateAnnoTele pure vs $ vacuous scope
      convertedType <- convertExpr t

      let abstr = teleAbstraction vs
          tele' = error "convertDefinitions"
            <$> Telescope (Vector.zipWith (\v e -> TeleArg (varHint v) () (abstract abstr e)) vs es)
          typeScope = error "convertDefinitions"
            <$> abstract abstr convertedType
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
  :: Sized.Definition Expr Void
  -> ClosureConvert (Sized.Definition Expr Void)
convertDefinition (Sized.FunctionDef vis cl (Sized.Function tele scope)) = do
  vs <- forMTele tele $ \h () _ ->
    freeVar h ()

  es <- forMTele tele $ \_ () s ->
    convertExpr $ instantiateTele pure vs $ vacuous s

  let expr = instantiateAnnoTele pure vs $ vacuous scope
      abstr = teleAbstraction vs
      tele'' = error "convertFunction" <$> Telescope (Vector.zipWith (\v e -> TeleArg (varHint v) () (abstract abstr e)) vs es)
  expr' <- convertAnnoExpr expr
  let scope' = abstractAnno abstr expr'
  return
    $ Sized.FunctionDef vis cl
    $ Sized.Function tele''
    $ error "convertDefinition Function" <$> scope'
convertDefinition (Sized.ConstantDef vis (Sized.Constant expr@(Anno (Global glob) sz))) = do
  msig <- convertedSignature glob
  expr' <- case msig of
    Nothing -> convertAnnoExpr $ vacuous expr
    Just _ -> do
      sz' <- convertExpr $ vacuous sz
      return $ Anno (Global glob) sz'
  return
    $ Sized.ConstantDef vis
    $ Sized.Constant
    $ error "convertDefinition Constant" <$> expr'
convertDefinition (Sized.ConstantDef vis (Sized.Constant expr)) = do
  expr' <- convertAnnoExpr $ vacuous expr
  return
    $ Sized.ConstantDef vis
    $ Sized.Constant
    $ error "convertDefinition Constant" <$> expr'
convertDefinition Sized.AliasDef = return Sized.AliasDef

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
    let bodyScope' = abstract1 v bodyExpr'
    return $ Let h e' bodyScope'
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
knownCall f (tele, returnTypeScope) args
  | numArgs < arity = do
    target <- getTarget
    piRep <- Lit . TypeRep <$> getPiRep
    intRep <- Lit . TypeRep <$> getIntRep
    fNumArgs <- liftClosureFun f (tele, returnTypeScope) numArgs
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
liftClosureFun f (tele, returnTypeScope) numCaptured = do
  vs <- forTeleWithPrefixM tele $ \h _ s vs -> do
    v <- freeVar h ()
    return (v, instantiateTele pure (fst <$> vs) $ vacuous s)

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
      funAbstr = teleAbstraction $ fst <$> funParams
      funTele = Telescope $ (\(v, t) -> TeleArg (varHint v) () (abstract funAbstr t)) <$> funParams

  unused1 <- freeVar "unused" ()
  unused2 <- freeVar "unused" ()
  let clArgs
        = Vector.cons (unused1, piRep)
        $ Vector.cons (unused2, intRep)
        capturedArgs
      clAbstr = teleAbstraction $ fst <$> clArgs
      clTele = Telescope $ (\(v, t) -> TeleArg (varHint v) () (abstract clAbstr t)) <$> clArgs
      funArgs = capturedArgs <> remainingParams'
      funArgs' = flip fmap funArgs $ \(v, t) -> Anno (pure v) t

  let returnType = instantiateTele pure (fst <$> vs) $ vacuous returnTypeScope
      fReturnType
        | any (\x -> HashSet.member x $ toHashSet returnType) $ fst <$> capturedArgs =
          Case (Anno (Builtin.deref $ pure this) (Global "ClosureConvert.knownCall.unknownSize"))
          $ ConBranches $ pure $ ConBranch Builtin.Closure clTele
          $ abstract clAbstr returnType
        | otherwise = returnType

  liftThing
    $ fmap (error "liftClosureFun")
    $ Sized.Function funTele
    $ abstractAnno funAbstr
    $ Anno
      (Case (Anno (Builtin.deref $ pure this) (Global "ClosureConvert.knownCall.unknownSize"))
      $ ConBranches $ pure $ ConBranch Builtin.Closure clTele
      $ abstract clAbstr
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
        abstr = teleAbstraction vs
        tele'' = Telescope $ Vector.zipWith (\v e -> TeleArg (varHint v) () $ abstract abstr e) vs es
    brExpr' <- convertExpr brExpr
    let brScope' = abstract abstr brExpr'
    return $ ConBranch qc tele'' brScope'
convertBranches (LitBranches lbrs def) = LitBranches
  <$> mapM (\(LitBranch l e) -> LitBranch l <$> convertExpr e) lbrs <*> convertExpr def
