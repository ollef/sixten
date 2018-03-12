{-# LANGUAGE FlexibleContexts, MonadComprehensions, OverloadedStrings #-}
module Analysis.ReturnDirection where

import Control.Monad
import Control.Monad.ST
import Data.Bitraversable
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.STRef
import qualified Data.Text.Prettyprint.Doc as PP
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import Data.Void

import FreeVar
import Syntax hiding (Definition, bitraverseDefinition)
import Syntax.Sized.Anno
import Syntax.Sized.Definition
import Syntax.Sized.Lifted
import Util
import VIX

data MetaReturnIndirect
  = MProjection
  | MOutParam
  | MRef (STRef RealWorld (Maybe MetaReturnIndirect))
  deriving Eq

type RetDirM = ReturnDirection MetaReturnIndirect

existsMetaReturnIndirect :: VIX MetaReturnIndirect
existsMetaReturnIndirect = liftST $ MRef <$> newSTRef Nothing

instance Show MetaReturnIndirect where
  show MProjection = "MProjection"
  show MOutParam = "MOutParam"
  show (MRef _) = "MRef"

fromReturnIndirect :: ReturnIndirect -> MetaReturnIndirect
fromReturnIndirect Projection = MProjection
fromReturnIndirect OutParam = MOutParam

toReturnIndirect :: ReturnIndirect -> MetaReturnIndirect -> VIX ReturnIndirect
toReturnIndirect def m = do
  m' <- normaliseMetaReturnIndirect m
  return $ case m' of
    MProjection -> Projection
    MOutParam -> OutParam
    MRef _ -> def

normaliseMetaReturnIndirect :: MetaReturnIndirect -> VIX MetaReturnIndirect
normaliseMetaReturnIndirect MProjection = return MProjection
normaliseMetaReturnIndirect MOutParam = return MOutParam
normaliseMetaReturnIndirect m@(MRef ref) = do
  sol <- liftST $ readSTRef ref
  case sol of
    Nothing -> return m
    Just m' -> do
      m'' <- normaliseMetaReturnIndirect m'
      liftST $ writeSTRef ref $ Just m''
      return m''

maxMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> VIX MetaReturnIndirect
maxMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  maxMetaReturnIndirect' m1' m2'

maxMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> VIX MetaReturnIndirect
maxMetaReturnIndirect' MOutParam _ = return MOutParam
maxMetaReturnIndirect' _ MOutParam = return MOutParam
maxMetaReturnIndirect' MProjection m = return m
maxMetaReturnIndirect' m MProjection = return m
maxMetaReturnIndirect' m@(MRef ref1) (MRef ref2) | ref1 == ref2 = return m
maxMetaReturnIndirect' m@(MRef _) (MRef ref2) = do
  liftST $ writeSTRef ref2 $ Just m
  return m

unifyMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> VIX ()
unifyMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  unifyMetaReturnIndirect' m1' m2'

unifyMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> VIX ()
unifyMetaReturnIndirect' m1 m2 | m1 == m2 = return ()
unifyMetaReturnIndirect' m (MRef ref2) = liftST $ writeSTRef ref2 $ Just m
unifyMetaReturnIndirect' (MRef ref1) m = liftST $ writeSTRef ref1 $ Just m
unifyMetaReturnIndirect' m1 m2 = internalError $ "unifyMetaReturnIndirect" PP.<+> shower (m1, m2)

type Location = MetaReturnIndirect

data MetaData = MetaData
  { metaLocation :: !Location
  , metaFunSig :: Maybe (RetDirM, Vector Direction)
  } deriving Show

type MetaVar = FreeVar MetaData

exists :: NameHint -> Location -> Maybe (RetDirM, Vector Direction) -> VIX MetaVar
exists h loc call = freeVar h $ MetaData loc call

infer
  :: Expr MetaVar
  -> VIX (Expr MetaVar, Location)
infer expr = case expr of
  Var v -> return (expr, metaLocation $ varData v)
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
    v <- exists h eloc Nothing
    (s', sloc) <- infer $ instantiate1 (pure v) s
    return (Let h e' $ abstract1 v s', sloc)
  Case e brs -> do
    (e', eloc) <- inferAnno e
    (brs', loc) <- inferBranches eloc brs
    return (Case e' brs', loc)
  ExternCode c retType -> do
    (retType', _) <- infer retType
    c' <- mapM (fmap fst . inferAnno) c
    return (ExternCode c' retType', MOutParam)

inferAnno :: Anno Expr MetaVar -> VIX (Anno Expr MetaVar, Location)
inferAnno (Anno e t) = do
  (e', loc) <- infer e
  (t', _) <- infer t
  return (Anno e' t', loc)

inferCall
  :: (Expr MetaVar -> Vector (Anno Expr MetaVar) -> Expr MetaVar)
  -> ReturnDirection MetaReturnIndirect
  -> Vector Direction
  -> Expr MetaVar
  -> Vector (Anno Expr MetaVar)
  -> VIX (Expr MetaVar, MetaReturnIndirect)
inferCall con (ReturnIndirect mretIndirect) argDirs f es = do
  (f', _) <- infer f
  locatedEs <- mapM inferAnno es
  let es' = fst <$> locatedEs
      locs = [l | ((_, l), Indirect) <- Vector.zip locatedEs argDirs]
  loc <- foldM maxMetaReturnIndirect mretIndirect locs
  return (con f' es', loc)
inferCall con _ _ f es = do
  (f', _) <- infer f
  locatedEs <- mapM inferAnno es
  let es' = fst <$> locatedEs
  return (con f' es', MOutParam)

inferBranches
  :: Location
  -> Branches () Expr MetaVar
  -> VIX (Branches () Expr MetaVar, Location)
inferBranches loc (ConBranches cbrs) = do
  locatedCBrs <- forM cbrs $ \(ConBranch c tele brScope) -> do
    vs <- forMTele tele $ \h _ _ -> exists h loc Nothing
    let abstr = abstract $ teleAbstraction vs
        br = instantiateTele pure vs brScope
    sizes <- forMTele tele $ \_ _ s -> do
      let sz = instantiateTele pure vs s
      (sz', _szLoc)  <- infer sz
      return sz'
    tele' <- forM (Vector.zip vs sizes) $ \(v, sz) ->
      return $ TeleArg (varHint v) () $ abstr sz
    (br', brLoc) <- infer br
    let brScope' = abstr br'
    return (ConBranch c (Telescope tele') brScope', brLoc)
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
  :: Expr MetaVar
  -> VIX (Expr MetaVar, (RetDirM, Vector Direction))
inferFunction expr = case expr of
  Var v -> return (expr, fromMaybe def $ metaFunSig $ varData v)
  Global g -> do
    sig <- signature g
    case sig of
      Just (FunctionSig _ retDir argDirs) -> return (Global g, (fromReturnIndirect <$> retDir, argDirs))
      Just (ConstantSig _) -> def
      Just (AliasSig aliasee) -> inferFunction $ Global aliasee
      Nothing -> error "ReturnDirection.inferFunction no sig"
  _ -> return def
  where
    def = error "ReturnDirection.inferFunction non-function"

inferDefinition
  :: MetaVar
  -> Definition Expr MetaVar
  -> VIX (Definition Expr MetaVar, Signature MetaReturnIndirect)
inferDefinition FreeVar {varData = MetaData {metaFunSig = Just (retDir, argDirs)}} (FunctionDef vis cl (Function args s)) = do
  vs <- forMTele args $ \h _ _ -> exists h MProjection Nothing
  let abstr = teleAbstraction vs
  args' <- forMTele args $ \h d szScope -> do
    let sz = instantiateTele pure vs szScope
    (sz', _szLoc) <- infer sz
    let szScope' = abstract abstr sz'
    return $ TeleArg h d szScope'
  let e = instantiateAnnoTele pure vs s
  (e', loc) <- inferAnno e
  case retDir of
    ReturnIndirect m -> do
      glbdir <- maxMetaReturnIndirect loc m
      unifyMetaReturnIndirect glbdir m
    ReturnDirect _ -> return ()
  let s' = abstractAnno abstr e'
  return (FunctionDef vis cl $ Function (Telescope args') s', FunctionSig SixtenCompatible retDir argDirs)
inferDefinition _ (ConstantDef _ (Constant (Anno (Global glob) _))) =
  return (AliasDef, AliasSig glob)
inferDefinition _ (ConstantDef vis (Constant e)) = do
  (e', _loc) <- inferAnno e
  return (ConstantDef vis $ Constant e', ConstantSig $ typeDir $ typeAnno e)
inferDefinition _ _ = error "ReturnDirection.inferDefinition"

generaliseDefs
  :: Vector (Definition Expr MetaVar, Signature MetaReturnIndirect)
  -> VIX (Vector (Definition Expr MetaVar, Signature ReturnIndirect))
generaliseDefs
  = traverse
  $ bitraverse pure (traverse $ toReturnIndirect Projection)

inferRecursiveDefs
  :: Vector (QName, Definition Expr Void)
  -> VIX (Vector (QName, Definition Expr Void, Signature ReturnIndirect))
inferRecursiveDefs defs = do
  let names = fst <$> defs

  evars <- Vector.forM defs $ \(v, d) -> do
    logPretty 30 "InferDirection.inferRecursiveDefs 1" (v, shower <$> d)
    let h = fromQName v
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
    exists h MProjection funSig'

  let nameIndex = hashedElemIndex names
      expose name = case nameIndex name of
        Nothing -> global name
        Just index -> pure
          $ fromMaybe (error "InferDirection.inferRecursiveDefs expose")
          $ evars Vector.!? index

  let exposedDefs = flip Vector.map defs $ \(_, e) ->
        bound absurd expose e

  inferredDefs <- Vector.forM (Vector.zip evars exposedDefs) $ \(v, d) -> do
    logPretty 30 "InferDirection.inferRecursiveDefs 2" (show v, shower <$> d)
    inferDefinition v d

  genDefs <- generaliseDefs inferredDefs

  let varIndex = hashedElemIndex evars
      unexpose evar = case varIndex evar of
        Nothing -> pure evar
        Just index -> global
          $ fromMaybe (error "inferRecursiveDefs 2")
          $ names Vector.!? index
      vf :: MetaVar -> VIX b
      vf v = internalError $ "inferRecursiveDefs" PP.<+> shower v

  forM (Vector.zip names genDefs) $ \(name, (def ,sig)) -> do
    let unexposedDef = bound unexpose global def
    unexposedDef' <- traverse vf unexposedDef
    return (name, unexposedDef', sig)
