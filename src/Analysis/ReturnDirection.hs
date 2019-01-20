{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Analysis.ReturnDirection where

import qualified Prelude(show)
import Protolude hiding (Location, MetaData)

import Data.Bitraversable
import Data.IORef
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Driver.Query
import Effect
import Effect.Context as Context
import Syntax hiding (Definition)
import Syntax.Sized.Anno
import Syntax.Sized.Definition
import Syntax.Sized.Lifted
import Util
import VIX

data MetaReturnIndirect
  = MProjection
  | MOutParam
  | MRef !(IORef (Maybe MetaReturnIndirect))
  deriving Eq

type RetDirM = ReturnDirection MetaReturnIndirect

existsMetaReturnIndirect :: Infer MetaReturnIndirect
existsMetaReturnIndirect = liftIO $ MRef <$> newIORef Nothing

instance Show MetaReturnIndirect where
  show MProjection = "MProjection"
  show MOutParam = "MOutParam"
  show (MRef _) = "MRef"

fromReturnIndirect :: ReturnIndirect -> MetaReturnIndirect
fromReturnIndirect Projection = MProjection
fromReturnIndirect OutParam = MOutParam

toReturnIndirect :: ReturnIndirect -> MetaReturnIndirect -> Infer ReturnIndirect
toReturnIndirect def m = do
  m' <- normaliseMetaReturnIndirect m
  return $ case m' of
    MProjection -> Projection
    MOutParam -> OutParam
    MRef _ -> def

normaliseMetaReturnIndirect :: MetaReturnIndirect -> Infer MetaReturnIndirect
normaliseMetaReturnIndirect MProjection = return MProjection
normaliseMetaReturnIndirect MOutParam = return MOutParam
normaliseMetaReturnIndirect m@(MRef ref) = do
  sol <- liftIO $ readIORef ref
  case sol of
    Nothing -> return m
    Just m' -> do
      m'' <- normaliseMetaReturnIndirect m'
      liftIO $ writeIORef ref $ Just m''
      return m''

maxMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> Infer MetaReturnIndirect
maxMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  maxMetaReturnIndirect' m1' m2'

maxMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> Infer MetaReturnIndirect
maxMetaReturnIndirect' MOutParam _ = return MOutParam
maxMetaReturnIndirect' _ MOutParam = return MOutParam
maxMetaReturnIndirect' MProjection m = return m
maxMetaReturnIndirect' m MProjection = return m
maxMetaReturnIndirect' m@(MRef ref1) (MRef ref2) | ref1 == ref2 = return m
maxMetaReturnIndirect' m@(MRef _) (MRef ref2) = do
  liftIO $ writeIORef ref2 $ Just m
  return m

unifyMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> Infer ()
unifyMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  unifyMetaReturnIndirect' m1' m2'

unifyMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> Infer ()
unifyMetaReturnIndirect' m1 m2 | m1 == m2 = return ()
unifyMetaReturnIndirect' m (MRef ref2) = liftIO $ writeIORef ref2 $ Just m
unifyMetaReturnIndirect' (MRef ref1) m = liftIO $ writeIORef ref1 $ Just m
unifyMetaReturnIndirect' m1 m2 = panic $ "unifyMetaReturnIndirect " <> shower (m1, m2)

type Location = MetaReturnIndirect

data MetaData = MetaData
  { metaLocation :: !Location
  , metaFunSig :: Maybe (RetDirM, Vector Direction)
  } deriving Show

type Infer = ReaderT (ContextEnvT MetaData VIX.Env) (Sequential (Task Query))

infer
  :: Expr FreeVar
  -> Infer (Expr FreeVar, Location)
infer expr = case expr of
  Var v -> do
    metaData <- Context.lookupType v
    return (expr, metaLocation metaData)
  Global _ -> return (expr, MProjection)
  Lit _ -> return (expr, MOutParam)
  Con c es -> do
    es' <- mapM inferAnno es
    return (Con c $ fst <$> es', MOutParam)
  Call f es -> do
    (f', (retDir, argDirs)) <- inferFunction f
    inferCall Call retDir argDirs f' es
  PrimCall retDir f es -> do
    let (argDirs, args) = Vector.unzip es
    inferCall
      (\f' es' -> PrimCall retDir f' $ Vector.zip argDirs es')
      (fromReturnIndirect <$> retDir)
      argDirs
      f
      args
  Let h e s -> do
    (e', eloc) <- inferAnno e
    Context.freshExtend (binding h Explicit $ MetaData eloc Nothing) $ \v -> do
      (s', sloc) <- infer $ instantiate1 (pure v) s
      res <- letTyped v e' s'
      return (res, sloc)
  Case e brs -> do
    (e', eloc) <- inferAnno e
    (brs', loc) <- inferBranches eloc brs
    return (Case e' brs', loc)
  ExternCode c retType -> do
    (retType', _) <- infer retType
    c' <- mapM (fmap fst . inferAnno) c
    return (ExternCode c' retType', MOutParam)

inferAnno :: Anno Expr FreeVar -> Infer (Anno Expr FreeVar, Location)
inferAnno (Anno e t) = do
  (e', loc) <- infer e
  (t', _) <- infer t
  return (Anno e' t', loc)

inferCall
  :: (Expr FreeVar -> Vector (Anno Expr FreeVar) -> Expr FreeVar)
  -> ReturnDirection MetaReturnIndirect
  -> Vector Direction
  -> Expr FreeVar
  -> Vector (Anno Expr FreeVar)
  -> Infer (Expr FreeVar, MetaReturnIndirect)
inferCall con (ReturnIndirect mretIndirect) argDirs f es = do
  (f', _) <- infer f
  locatedEs <- mapM inferAnno es
  let es' = fst <$> locatedEs
      locs
        = (\((_, l), _) -> l)
        <$> Vector.filter ((== Indirect) . snd) (Vector.zip locatedEs argDirs)
  loc <- foldM maxMetaReturnIndirect mretIndirect locs
  return (con f' es', loc)
inferCall con _ _ f es = do
  (f', _) <- infer f
  locatedEs <- mapM inferAnno es
  let es' = fst <$> locatedEs
  return (con f' es', MOutParam)

inferBranches
  :: Location
  -> Branches Expr FreeVar
  -> Infer (Branches Expr FreeVar, Location)
inferBranches loc (ConBranches cbrs) = do
  locatedCBrs <- forM cbrs $ \(ConBranch c tele brScope) ->
    teleMapExtendContext tele (pure . const (MetaData loc Nothing)) $ \vs -> do
      let br = instantiateTele pure vs brScope
      sizes <- forMTele tele $ \_ _ s -> do
        let sz = instantiateTele pure vs s
        (sz', _szLoc)  <- infer sz
        return sz'
      (br', brLoc) <- infer br
      res <- typedConBranch c (Vector.zip vs sizes) br'
      return (res, brLoc)
  let (cbrs', brLocs) = NonEmpty.unzip locatedCBrs
  brLoc <- foldM maxMetaReturnIndirect MProjection brLocs
  return (ConBranches cbrs', brLoc)
inferBranches _loc (LitBranches lbrs def) = do
  locatedLbrs <- forM lbrs $ \(LitBranch lit e) -> do
    (e', loc) <- infer e
    return (LitBranch lit e', loc)
  (def', defloc) <- infer def
  let (lbrs', locs) = NonEmpty.unzip locatedLbrs
  loc <- foldM maxMetaReturnIndirect defloc locs
  return (LitBranches lbrs' def', loc)

inferFunction
  :: Expr FreeVar
  -> Infer (Expr FreeVar, (RetDirM, Vector Direction))
inferFunction expr = case expr of
  Var v -> do
    metaData <- Context.lookupType v
    return (expr, fromMaybe def $ metaFunSig metaData)
  Global g -> do
    sig <- fetch $ DirectionSignature g
    case sig of
      Just (FunctionSig _ retDir argDirs) -> return (Global g, (fromReturnIndirect <$> retDir, argDirs))
      Just (ConstantSig _) -> def
      Just (AliasSig aliasee) -> inferFunction $ Global aliasee
      Nothing -> panic "ReturnDirection.inferFunction no sig"
  _ -> return def
  where
    def = panic "ReturnDirection.inferFunction non-function"

inferDefinition
  :: Binding MetaData
  -> Definition Expr FreeVar
  -> Infer (Definition Expr FreeVar, Signature MetaReturnIndirect)
inferDefinition Binding {_type = MetaData {metaFunSig = Just (retDir, argDirs)}} (FunctionDef vis cl (Function args s)) =
  teleMapExtendContext args (pure . const (MetaData MProjection Nothing)) $ \vs -> do
    args' <- forMTele args $ \_ _ szScope -> do
      let sz = instantiateTele pure vs szScope
      (sz', _szLoc) <- infer sz
      return sz'
    let e = instantiateAnnoTele pure vs s
    (e', loc) <- inferAnno e
    case retDir of
      ReturnIndirect m -> do
        glbdir <- maxMetaReturnIndirect loc m
        unifyMetaReturnIndirect glbdir m
      ReturnDirect _ -> return ()
    fun <- typedFunction (Vector.zip vs args') e'
    return (FunctionDef vis cl fun, FunctionSig SixtenCompatible retDir argDirs)
inferDefinition _ (ConstantDef _ (Constant (Anno (Global glob) _))) =
  return (AliasDef, AliasSig glob)
inferDefinition _ (ConstantDef vis (Constant e)) = do
  (e', _loc) <- inferAnno e
  return (ConstantDef vis $ Constant e', ConstantSig $ typeDir $ typeAnno e)
inferDefinition _ _ = panic "ReturnDirection.inferDefinition"

generaliseDefs
  :: Vector (Definition Expr FreeVar, Signature MetaReturnIndirect)
  -> Infer (Vector (Definition Expr FreeVar, Signature ReturnIndirect))
generaliseDefs
  = traverse
  $ bitraverse pure (traverse $ toReturnIndirect Projection)

inferRecursiveDefs
  :: Vector (GName, Closed (Definition Expr))
  -> VIX (Vector (GName, Closed (Definition Expr), Signature ReturnIndirect))
inferRecursiveDefs defs = withContextEnvT $ do
  let names = fst <$> defs

  bindings_ <- Vector.forM defs $ \(v, Closed d) -> do
    logPretty "returndir" "InferDirection.inferRecursiveDefs 1" $ pure (v, d)
    let
      h = fromGName v
      funSig = case d of
        FunctionDef _ cl (Function args s) ->
          Just
            ( returnDir
            , forTele args $ \_ _ s' -> typeDir $ fromScope s'
            )
          where
            returnDir = case (cl, fromAnnoScope s) of
              (NonClosure, Anno _ t) -> toReturnDirection Nothing $ typeDir t
              _ -> ReturnIndirect (Just MOutParam)
        ConstantDef {} -> Nothing
        AliasDef -> Nothing
    funSig' <- traverse (bitraverse (traverse $ maybe existsMetaReturnIndirect pure) pure) funSig
    return $ binding h Explicit $ MetaData MProjection funSig'

  freshExtends bindings_ $ \evars -> do
    let
      nameIndex = hashedElemIndex names
      expose name = case nameIndex name of
        Nothing -> global name
        Just index -> pure
          $ fromMaybe (panic "InferDirection.inferRecursiveDefs expose")
          $ evars Vector.!? index

      exposedDefs = flip Vector.map defs $ \(_, Closed e) ->
        gbound expose e

    inferredDefs <- Vector.forM (Vector.zip bindings_ exposedDefs) $ \(b, d) -> do
      logPretty "returndir" "InferDirection.inferRecursiveDefs 2" $ traverse prettyVar d
      inferDefinition b d

    genDefs <- generaliseDefs inferredDefs

    let
      varIndex = hashedElemIndex evars
      unexpose evar = case varIndex evar of
        Nothing -> pure evar
        Just index -> global
          $ fromMaybe (panic "inferRecursiveDefs 2")
          $ names Vector.!? index
      vf :: FreeVar -> Infer b
      vf v = panic $ "inferRecursiveDefs " <> shower v

    forM (Vector.zip names genDefs) $ \(name, (def ,sig)) -> do
      let unexposedDef = def >>>= unexpose
      unexposedDef' <- traverse vf unexposedDef
      return (name, close identity unexposedDef', sig)
