module Analysis.ReturnDirection where

import Control.Monad
import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bitraversable
import Data.Function
import Data.Hashable
import qualified Data.List.NonEmpty as NonEmpty
import Data.STRef
import qualified Data.Vector as Vector
import Data.Vector(Vector)

import Syntax hiding (Definition, traverseDefinitionFirst, recursiveAbstractDefs, instantiateDef) -- TODO cleanup name conflicts
import Syntax.Sized.Lifted
import TCM

data MetaReturnIndirect
  = MProjection
  | MOutParam
  | MRef (STRef (World TCM) (Maybe MetaReturnIndirect))
  deriving Eq

type RetDirM = ReturnDirection MetaReturnIndirect

existsMetaReturnIndirect :: TCM MetaReturnIndirect
existsMetaReturnIndirect = liftST $ MRef <$> newSTRef Nothing

instance Show MetaReturnIndirect where
  show MProjection = "MProjection"
  show MOutParam = "MOutParam"
  show (MRef _) = "MRef"

fromReturnIndirect :: ReturnIndirect -> MetaReturnIndirect
fromReturnIndirect Projection = MProjection
fromReturnIndirect OutParam = MOutParam

toReturnIndirect :: ReturnIndirect -> MetaReturnIndirect -> TCM ReturnIndirect
toReturnIndirect def m = do
  m' <- normaliseMetaReturnIndirect m
  return $ case m' of
    MProjection -> Projection
    MOutParam -> OutParam
    MRef _ -> def

normaliseMetaReturnIndirect :: MetaReturnIndirect -> TCM MetaReturnIndirect
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

maxMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> TCM MetaReturnIndirect
maxMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  maxMetaReturnIndirect' m1' m2'

maxMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> TCM MetaReturnIndirect
maxMetaReturnIndirect' MOutParam _ = return MOutParam
maxMetaReturnIndirect' _ MOutParam = return MOutParam
maxMetaReturnIndirect' MProjection m = return m
maxMetaReturnIndirect' m MProjection = return m
maxMetaReturnIndirect' m@(MRef ref1) (MRef ref2) | ref1 == ref2 = return m
maxMetaReturnIndirect' m@(MRef _) (MRef ref2) = do
  liftST $ writeSTRef ref2 $ Just m
  return m

unifyMetaReturnIndirect :: MetaReturnIndirect -> MetaReturnIndirect -> TCM ()
unifyMetaReturnIndirect m1 m2 = do
  m1' <- normaliseMetaReturnIndirect m1
  m2' <- normaliseMetaReturnIndirect m2
  unifyMetaReturnIndirect' m1' m2'

unifyMetaReturnIndirect' :: MetaReturnIndirect -> MetaReturnIndirect -> TCM ()
unifyMetaReturnIndirect' m1 m2 | m1 == m2 = return ()
unifyMetaReturnIndirect' m (MRef ref2) = liftST $ writeSTRef ref2 $ Just m
unifyMetaReturnIndirect' (MRef ref1) m = liftST $ writeSTRef ref1 $ Just m
unifyMetaReturnIndirect' m1 m2 = throwError $ "unifyMetaReturnIndirect " ++ show (m1, m2)

type Location = MetaReturnIndirect

data MetaVar = MetaVar
  { metaHint :: !NameHint
  , metaId :: !Int
  , metaLocation :: !Location
  , metaReturnIndirect :: !MetaReturnIndirect -- ^ If callable.
  }

exists :: NameHint -> Location -> MetaReturnIndirect -> TCM MetaVar
exists h loc call = MetaVar h <$> fresh <*> pure loc <*> pure call

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Show MetaVar where
  show mv = "$" ++ show (metaId mv) ++ maybe "" fromName (unNameHint $ metaHint mv)

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

infer
  :: Expr ClosureDir MetaVar
  -> TCM (Expr RetDirM MetaVar, Location)
infer expr = case expr of
  Var v -> return (Var v, metaLocation v)
  Global g -> return (Global g, MProjection)
  Lit l -> return (Lit l, MProjection)
  Con c es -> do
    es' <- mapM infer es
    return (Con c $ fst <$> es', MOutParam)  -- TODO: Can be improved.
  Call ClosureDir f es -> locatedCall MOutParam (ReturnIndirect MOutParam) f es
  Call (NonClosureDir Void) f es -> directCall ReturnVoid f es
  Call (NonClosureDir Direct) f es -> directCall ReturnDirect f es
  Call (NonClosureDir Indirect) f es -> do
    returnDir <- inferIndirectReturnDir f
    (f', _) <- infer f
    locatedEs <- mapM (bitraverse infer pure) es
    let es' = (\((e, _), d) -> (e, d)) <$> locatedEs
        locs = (\((_, l), _) -> l) <$> locatedEs
    loc <- foldM maxMetaReturnIndirect returnDir locs
    return (Call (ReturnIndirect returnDir) f' es', loc)
  Let h e s -> do
    (e', eloc) <- infer e
    v <- exists h eloc MOutParam
    (s', sloc) <- infer $ instantiate1 (pure v) s
    return (Let h e' $ abstract1 v s', sloc)
  Case e brs -> do
    (e', eloc) <- infer e
    (brs', loc) <- inferBranches eloc brs
    return (Case e' brs', loc)
  Prim p -> do
    p' <- mapM (fmap fst . infer) p
    return (Prim p', MProjection) -- TODO?
  Sized sz e -> do
    (sz', _szLoc) <- infer sz
    (e', eLoc) <- infer e
    return (Sized sz' e', eLoc)
  where
    directCall = locatedCall MProjection
    locatedCall loc dir f es = do
      (f', _) <- infer f
      locatedEs <- mapM (bitraverse infer pure) es
      let es' = (\((e, _), d) -> (e, d)) <$> locatedEs
      return (Call dir f' es', loc)

inferBranches
  :: Location
  -> Branches c () (Expr ClosureDir) MetaVar
  -> TCM (Branches c () (Expr RetDirM) MetaVar, Location)
inferBranches loc (ConBranches cbrs) = do
  locatedCBrs <- forM cbrs $ \(c, tele, brScope) -> do
    vs <- forMTele tele $ \h _ _ -> exists h loc MOutParam
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
inferBranches loc (NoBranches typ) = do
  (typ', _loc) <- infer typ
  return (NoBranches typ', loc) -- TODO Is this location correct?

inferIndirectReturnDir
  :: Expr ClosureDir MetaVar
  -> TCM MetaReturnIndirect
inferIndirectReturnDir expr = case expr of
  Var v -> return $ metaReturnIndirect v
  Global g -> do
    dir <- returnDirection g
    return $ case dir of
      ReturnIndirect res -> fromReturnIndirect res
      _ -> MOutParam
  _ -> return MOutParam

inferDefinition
  :: MetaVar
  -> Definition ClosureDir (Expr ClosureDir) MetaVar
  -> TCM (Definition RetDirM (Expr RetDirM) MetaVar)
inferDefinition v (FunctionDef vis (Function mretDir args s)) = do
  vs <- forMTele args $ \h _ _ -> exists h MProjection MOutParam
  args' <- forMTele args $ \h d szScope -> do
    let sz = instantiateTele pure vs szScope
    (sz', _szLoc) <- infer sz
    let szScope' = abstract (teleAbstraction vs) sz'
    return (h, d, szScope')
  let e = instantiateTele pure vs s
      vdir = metaReturnIndirect v
  retDir <- case mretDir of
    ClosureDir -> do
      unifyMetaReturnIndirect MOutParam vdir
      return Indirect
    NonClosureDir retDir -> return retDir
  (e', loc) <- infer e
  glbdir <- maxMetaReturnIndirect loc vdir
  unifyMetaReturnIndirect glbdir vdir
  let retDir' = toReturnDirection vdir retDir
      s' = abstract (teleAbstraction vs) e'
  return $ FunctionDef vis $ Function retDir' (Telescope args') s'
inferDefinition _ (ConstantDef vis (Constant dir e))
  = ConstantDef vis . Constant dir . fst <$> infer e

generaliseDefs
  :: Vector (MetaVar, Definition RetDirM (Expr RetDirM) MetaVar)
  -> TCM (Vector (Definition RetDir (Expr RetDir) (Var Int MetaVar)))
generaliseDefs ds = do
  ds' <- traverse (bitraverse pure $ traverseDefinitionFirst $ traverse $ toReturnIndirect Projection) ds
  return $ recursiveAbstractDefs ds'

inferRecursiveDefs
  :: Vector (Name, Definition ClosureDir (Expr ClosureDir) (Var Int MetaVar))
  -> TCM (Vector (Definition RetDir (Expr RetDir) (Var Int MetaVar)))
inferRecursiveDefs ds = do
  evs <- Vector.forM ds $ \(v, d) -> do
    logPretty 30 "InferDirection.inferRecursiveDefs 1" (v, show <$> d)
    let h = fromName v
    exists h MProjection =<< existsMetaReturnIndirect
  let instantiatedDs = flip Vector.map ds $ \(_, e) ->
        instantiateDef (pure . (evs Vector.!)) e

  results <- flip Vector.imapM instantiatedDs $ \i d -> do
    let v = evs Vector.! i
    logPretty 30 "InferDirection.inferRecursiveDefs 2" (show v, show <$> d)
    d' <- inferDefinition v d
    return (v, d')

  generaliseDefs results
