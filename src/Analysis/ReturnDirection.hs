{-# LANGUAGE MonadComprehensions #-}
module Analysis.ReturnDirection where

import Control.Monad
import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bitraversable
import Data.Function
import Data.Hashable
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.STRef
import qualified Data.Vector as Vector
import Data.Vector(Vector)
import Data.Void

import Syntax hiding (Definition, bitraverseDefinition)
import Syntax.Sized.Definition
import Syntax.Sized.Lifted
import VIX

data MetaReturnIndirect
  = MProjection
  | MOutParam
  | MRef (STRef (World VIX) (Maybe MetaReturnIndirect))
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
unifyMetaReturnIndirect' m1 m2 = throwError $ "unifyMetaReturnIndirect " ++ show (m1, m2)

type Location = MetaReturnIndirect

data MetaVar = MetaVar
  { metaHint :: !NameHint
  , metaId :: !Int
  , metaLocation :: !Location
  , metaFunSig :: Maybe (RetDirM, Vector Direction)
  }

exists :: NameHint -> Location -> Maybe (RetDirM, Vector Direction) -> VIX MetaVar
exists h loc call = MetaVar h <$> fresh <*> pure loc <*> pure call

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Show MetaVar where
  show mv = "$" ++ show (metaId mv) ++ maybe "" fromName (unNameHint $ metaHint mv)

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

infer
  :: Expr MetaVar
  -> VIX (Expr MetaVar, Location)
infer expr = case expr of
  Var v -> return (expr, metaLocation v)
  Global _ -> return (expr, MProjection)
  Lit _ -> return (expr, MOutParam)
  Con c es -> do
    es' <- mapM infer es
    return (Con c $ fst <$> es', MOutParam)  -- TODO: Can be improved.
  Call f es -> do
    (retDir, argDirs) <- inferFunction f
    inferCall Call retDir argDirs f es
  PrimCall retDir f es -> do
    let (args, argDirs) = Vector.unzip es
    inferCall
      (\f' es' -> PrimCall retDir f' $ Vector.zip es' argDirs)
      (fromReturnIndirect <$> retDir)
      argDirs
      f
      args
  Let h e s -> do
    (e', eloc) <- infer e
    v <- exists h eloc Nothing
    (s', sloc) <- infer $ instantiate1 (pure v) s
    return (Let h e' $ abstract1 v s', sloc)
  Case e brs -> do
    (e', eloc) <- infer e
    (brs', loc) <- inferBranches eloc brs
    return (Case e' brs', loc)
  Anno e t -> do
    (e', eLoc) <- infer e
    (t', _tLoc) <- infer t
    return (Anno e' t', eLoc)
  ExternCode c -> do
    c' <- mapM (fmap fst . infer) c
    return (ExternCode c', MOutParam)

inferCall
  :: (Expr MetaVar -> Vector (Expr MetaVar) -> Expr MetaVar)
  -> ReturnDirection MetaReturnIndirect
  -> Vector Direction
  -> Expr MetaVar
  -> Vector (Expr MetaVar)
  -> VIX (Expr MetaVar, MetaReturnIndirect)
inferCall con (ReturnIndirect mretIndirect) argDirs f es = do
  (f', _) <- infer f
  locatedEs <- mapM infer es
  let es' = fst <$> locatedEs
      locs = [l | ((_, l), Indirect) <- Vector.zip locatedEs argDirs]
  loc <- foldM maxMetaReturnIndirect mretIndirect locs
  return (con f' es', loc)
inferCall con _ _ f es = do
  (f', _) <- infer f
  locatedEs <- mapM infer es
  let es' = fst <$> locatedEs
  return (con f' es', MOutParam)

inferBranches
  :: Location
  -> Branches c () Expr MetaVar
  -> VIX (Branches c () Expr MetaVar, Location)
inferBranches loc (ConBranches cbrs) = do
  locatedCBrs <- forM cbrs $ \(c, tele, brScope) -> do
    vs <- forMTele tele $ \h _ _ -> exists h loc Nothing
    let abstr = abstract $ teleAbstraction vs
        br = instantiateTele pure vs brScope
    sizes <- forMTele tele $ \_ _ s -> do
      let sz = instantiateTele pure vs s
      (sz', _szLoc)  <- infer sz
      return sz'
    tele' <- forM (Vector.zip vs sizes) $ \(v, sz) ->
      return (metaHint v, (), abstr sz)
    (br', brLoc) <- infer br
    let brScope' = abstr br'
    return ((c, Telescope tele', brScope'), brLoc)
  let (cbrs', brLocs) = NonEmpty.unzip locatedCBrs
  brLoc <- foldM maxMetaReturnIndirect MProjection brLocs
  return (ConBranches cbrs', brLoc)
inferBranches _loc (LitBranches lbrs def) = do
  locatedLbrs <- forM lbrs $ \(lit, e) -> do
    (e', loc) <- infer e
    return ((lit, e'), loc)
  (def', defloc) <- infer def
  let (lbrs', locs) = NonEmpty.unzip locatedLbrs
  loc <- foldM maxMetaReturnIndirect defloc locs
  return (LitBranches lbrs' def', loc)

inferFunction
  :: Expr MetaVar
  -> VIX (RetDirM, Vector Direction)
inferFunction expr = case expr of
  Var v -> return $ fromMaybe def $ metaFunSig v
  Global g -> do
    sig <- signature g
    return $ case sig of
      FunctionSig retDir argDirs -> (fromReturnIndirect <$> retDir, argDirs)
      _ -> def
  _ -> return def
  where
    def = error "ReturnDirection.inferFunction non-function"

inferDefinition
  :: MetaVar
  -> Definition Expr MetaVar
  -> VIX (Definition Expr MetaVar, Signature MetaReturnIndirect)
inferDefinition MetaVar {metaFunSig = Just (retDir, argDirs)} (FunctionDef vis cl (Function args s)) = do
  vs <- forMTele args $ \h _ _ -> exists h MProjection Nothing
  args' <- forMTele args $ \h d szScope -> do
    let sz = instantiateTele pure vs szScope
    (sz', _szLoc) <- infer sz
    let szScope' = abstract (teleAbstraction vs) sz'
    return (h, d, szScope')
  let e = instantiateTele pure vs s
  (e', loc) <- infer e
  case retDir of
    ReturnIndirect m -> do
      glbdir <- maxMetaReturnIndirect loc m
      unifyMetaReturnIndirect glbdir m
    ReturnDirect _ -> return ()
  let s' = abstract (teleAbstraction vs) e'
  return (FunctionDef vis cl $ Function (Telescope args') s', FunctionSig retDir argDirs)
inferDefinition _ (ConstantDef vis (Constant (Anno (Global glob) sz))) = do
  sig <- signature glob
  (sz', _szLoc) <- infer sz
  return (ConstantDef vis $ Constant $ Anno (Global glob) sz', fromReturnIndirect <$> sig)
inferDefinition _ (ConstantDef vis (Constant e)) = do
  (e', _loc) <- infer e
  return (ConstantDef vis $ Constant e', ConstantSig $ sizeDir $ sizeOf e)
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
    logPretty 30 "InferDirection.inferRecursiveDefs 1" (v, show <$> d)
    let h = fromQName v
        funSig = case d of
          FunctionDef _ cl (Function args s) ->
            Just
              ( returnDir
              , forTele args $ \_ _ s' -> sizeDir $ fromScope s'
              )
            where
              returnDir = case (cl, fromScope s) of
                (NonClosure, Anno _ t) -> toReturnDirection Nothing $ sizeDir t
                _ -> ReturnIndirect (Just MOutParam)
          ConstantDef {} -> Nothing
    funSig' <- traverse (bitraverse (traverse $ maybe existsMetaReturnIndirect pure) pure) funSig
    exists h MProjection funSig'

  let expose name = case Vector.elemIndex name names of
        Nothing -> global name
        Just index -> pure
          $ fromMaybe (error "InferDirection.inferRecursiveDefs expose")
          $ evars Vector.!? index

  let exposedDefs = flip Vector.map defs $ \(_, e) ->
        bound absurd expose e

  inferredDefs <- Vector.forM (Vector.zip evars exposedDefs) $ \(v, d) -> do
    logPretty 30 "InferDirection.inferRecursiveDefs 2" (show v, show <$> d)
    inferDefinition v d

  genDefs <- generaliseDefs inferredDefs

  let unexpose evar = case Vector.elemIndex evar evars of
        Nothing -> pure evar
        Just index -> global
          $ fromMaybe (error "inferRecursiveDefs 2")
          $ names Vector.!? index
      vf :: MetaVar -> VIX b
      vf v = throwError $ "inferRecursiveDefs " ++ show v

  forM (Vector.zip names genDefs) $ \(name, (def ,sig)) -> do
    let unexposedDef = bound unexpose global def
    unexposedDef' <- traverse vf unexposedDef
    return (name, unexposedDef', sig)
