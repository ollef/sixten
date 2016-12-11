{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RecursiveDo, TypeFamilies, ViewPatterns #-}
module InferErasability where

import Control.Monad.Except
import Control.Monad.ST.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Function
import Data.Hashable
import Data.Monoid
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import Data.STRef
import Data.Vector(Vector)
import qualified Data.Vector as Vector

import qualified Builtin
import Syntax
import Syntax.Abstract
import TCM
import TypeOf
import Util
import Meta(MetaVary(..))
import Normalise

data MetaErasability
  = MErased
  | MRetained
  | MRef (STRef (World TCM) (Maybe MetaErasability))
  deriving Eq

instance Show MetaErasability where
  show MErased = "MErased"
  show MRetained = "MRetained"
  show (MRef _) = "MRef"

minMetaErasability :: MetaErasability -> MetaErasability -> TCM MetaErasability
minMetaErasability MErased _ = return MErased
minMetaErasability _ MErased = return MErased
minMetaErasability x MRetained = return x
minMetaErasability MRetained x = return x
minMetaErasability m@(MRef ref1) (MRef ref2) | ref1 == ref2 = return m
minMetaErasability m@(MRef ref1) (MRef ref2) = do
  liftST $ writeSTRef ref2 $ Just $ MRef ref1
  return m

showMetaErasability :: MetaErasability -> TCM String
showMetaErasability = fmap show . normaliseMetaErasability

instance PrettyAnnotation MetaErasability where
  prettyAnnotation MErased = prettyTightApp "~"
  prettyAnnotation MRetained = prettyTightApp "!"
  prettyAnnotation (MRef _) = prettyTightApp "?"

normaliseMetaErasability :: MetaErasability -> TCM MetaErasability
normaliseMetaErasability MErased = return MErased
normaliseMetaErasability MRetained = return MRetained
normaliseMetaErasability m@(MRef ref) = do
  sol <- liftST $ readSTRef ref
  case sol of
    Nothing -> return m
    Just m' -> do
      m'' <- normaliseMetaErasability m'
      liftST $ writeSTRef ref $ Just m''
      return m''

existsMetaErasability :: TCM MetaErasability
existsMetaErasability = liftST $ MRef <$> newSTRef Nothing

fromErasability :: Erasability -> MetaErasability
fromErasability er = case er of
  Erased -> MErased
  Retained -> MRetained

toErasability :: Erasability -> MetaErasability -> TCM Erasability
toErasability def er = do
  er' <- normaliseMetaErasability er
  return $ case er' of
    MErased -> Erased
    MRetained -> Retained
    MRef _ -> def

data MetaVar = MetaVar
  { metaId :: !Int
  , metaType :: Expr MetaErasability MetaVar
  , metaHint :: !NameHint
  , metaErasability :: MetaErasability
  }

instance Hashable MetaVar where
  hashWithSalt s = hashWithSalt s . metaId

instance Eq MetaVar where
  (==) = (==) `on` metaId

instance Ord MetaVar where
  compare = compare `on` metaId

instance Show MetaVar where
  show (MetaVar i _ h _) = "$" ++ show i ++ maybe mempty fromName (unNameHint h)

instance Meta.MetaVary (Expr MetaErasability) MetaVar where
  type MetaData (Expr MetaErasability) MetaVar = MetaErasability
  forall h er typ = do
    i <- fresh
    return $ MetaVar i typ h er
  refineVar v _ = return $ pure v
  metaVarType = metaType

instance Context (Expr MetaErasability) where
  definition = fmap (bimap (definitionFirst fromErasability) (first fromErasability)) . definition
  qconstructor = fmap (first fromErasability) . qconstructor
  typeOfSize = first fromErasability . typeOfSize

type AbstractM a = Expr a MetaVar
type ErasableM = Expr MetaErasability MetaVar

subErasability :: MetaErasability -> MetaErasability -> TCM ()
subErasability m1 m2 = do
  m1' <- normaliseMetaErasability m1
  m2' <- normaliseMetaErasability m2
  subErasability' m1' m2'

subErasability' :: MetaErasability -> MetaErasability -> TCM ()
subErasability' _ MErased = return ()
subErasability' MRetained _ = return ()
subErasability' MErased MRetained = throwError "subErasability"
subErasability' MErased (MRef ref) = liftST $ writeSTRef ref $ Just MErased
subErasability' (MRef ref) MRetained = liftST $ writeSTRef ref $ Just MRetained
subErasability' (MRef ref1) (MRef ref2) | ref1 == ref2 = return ()
subErasability' (MRef ref1) (MRef ref2) = liftST $ writeSTRef ref2 $ Just $ MRef ref1

logErasable :: Int -> String -> ErasableM -> TCM ()
logErasable v s e = whenVerbose v $ do
  e' <- bitraverse normaliseMetaErasability pure e
  logPretty v s $ show <$> e'

check :: PrettyAnnotation a => MetaErasability -> AbstractM a -> ErasableM -> TCM ErasableM
check er expr typ = do
  ers <- showMetaErasability er
  logPretty 20 ("check e " ++ ers) $ show <$> expr
  logPretty 20 ("check t " ++ ers) $ show <$> typ
  modifyIndent succ
  (expr', exprType) <- infer er expr
  f <- subtype exprType typ
  modifyIndent pred
  let res = f expr'
  logErasable 20 "check res e" res
  return res

inferType
  :: PrettyAnnotation a
  => MetaErasability
  -> AbstractM a
  -> TCM (ErasableM, ErasableM)
inferType er typ = do
  ers <- showMetaErasability er
  logPretty 20 ("inferType " ++ ers) $ show <$> typ
  modifyIndent succ
  (resType, resTypeType) <- case typ of
    Pi h _ argType retTypeScope -> do
      modifyIndent succ
      argEr <- existsMetaErasability
      argType' <- inferArgType argEr argType
      x <- forall h argEr argType'
      let retType = instantiate1 (pure x) retTypeScope
      (retType', _) <- inferType er retType
      modifyIndent pred
      return (Pi h argEr argType' $ abstract1 x retType', first fromErasability $ Builtin.TypeE $ Lit 1)
    _ -> infer er typ
  modifyIndent pred
  logErasable 20 "inferType res" resType
  return (resType, resTypeType)

inferArgType
  :: PrettyAnnotation a
  => MetaErasability
  -> AbstractM a
  -> TCM ErasableM
inferArgType argEr argType = do
  (argType', argTypeType) <- infer MErased argType
  case argEr of
    MErased -> return ()
    _ -> void $ infer argEr argTypeType -- retain the size
  return argType'

retainSize
  :: MetaErasability
  -> ErasableM
  -> TCM ()
retainSize argEr argType = do
  argTypeType <- typeOf argType
  case argEr of
    MErased -> return ()
    _ | Set.null $ toSet argTypeType -> return ()
      | otherwise -> void $ infer argEr argTypeType

infer
  :: PrettyAnnotation a
  => MetaErasability
  -> AbstractM a
  -> TCM (ErasableM, ErasableM)
infer er expr = do
  ers <- showMetaErasability er
  logPretty 20 ("infer " ++ ers) $ show <$> expr
  modifyIndent succ
  (resExpr, resType) <- case expr of
    Var v -> do
      subErasability (metaErasability v) er
      return (Var v, metaType v)
    Global g -> do
      (_, typ) <- definition g
      return (Global g, first fromErasability typ)
    Con c -> do
      typ <- qconstructor c
      return (Con c, first fromErasability typ)
    Lit l -> return (Lit l, Builtin.Size)
    Pi h _ argType retTypeScope -> do
      argEr <- case pisView argType of
            (_,  appsView . fromScope -> (Global Builtin.TypeName, _)) -> existsMetaErasability
            _ -> return MRetained
      argType' <- inferArgType argEr argType
      x <- forall h argEr argType'
      let retType = instantiate1 (pure x) retTypeScope
      (retType', _) <- infer MErased retType -- since we know this is a type
      return (Pi h argEr argType' $ abstract1 x retType', first fromErasability $ Builtin.TypeE $ Lit 1)
    Lam h _ argType retScope -> do
      (argType', _argTypeType) <- infer MErased argType
      argEr <- existsMetaErasability
      x <- forall h argEr argType'
      let ret = instantiate1 (pure x) retScope
      (ret', retType) <- infer er ret
      retainSize er retType
      return
        ( Lam h argEr argType' $ abstract1 x ret'
        , Pi h argEr argType' $ abstract1 x retType
        )
    App fun _ arg -> do
      (fun', funType) <- infer er fun
      funType' <- whnf funType
      case funType' of
        Pi _ argEr argType s -> do
          er' <- minMetaErasability er argEr
          retainSize er' argType
          arg' <- check er' arg argType
          let retType = instantiate1 arg' s
          retainSize er retType
          return (App fun' argEr arg', retType)
        _ -> throwError "InferErasability: Expected function"
    Case e brs -> do
      (e', _eType) <- infer er e
      (brs', typ) <- inferBranches er brs
      return (Case e' brs', typ)
  modifyIndent pred
  logErasable 20 "infer res" resExpr
  logErasable 20 "      res" resType
  return (resExpr, resType)

inferBranches
  :: PrettyAnnotation a
  => MetaErasability
  -> Branches QConstr a (Expr a) MetaVar
  -> TCM (Branches QConstr MetaErasability (Expr MetaErasability) MetaVar, ErasableM)
inferBranches er (ConBranches cbrs) = do
  cbrs' <- forM cbrs $ \(c@(QConstr dataTypeName _), tele, brScope) -> mdo
    (_, dataTypeType) <- definition dataTypeName
    let numParams = teleLength $ telescope (dataTypeType :: ErasableM)
    conType <- qconstructor c
    let (argTypes, _ret) = pisView (conType :: ExprE MetaVar)
    vs <- iforMTele tele $ \i h _ s -> do
      logVerbose 30 $ shower $ teleAnnotations argTypes
      let argEr = fromErasability $ teleAnnotations argTypes Vector.! (i + numParams)
          typ = instantiateTele pure vs s
      typ' <- inferArgType argEr typ
      forall h argEr typ'
    let abstr = abstract $ teleAbstraction vs
        br = instantiateTele pure vs brScope
    tele' <- forM vs $ \v -> return (metaHint v, metaErasability v, abstr $ metaType v)
    (br', retType) <- infer er br
    let brScope' = abstr br'
    return ((c, Telescope tele', brScope'), retType)
  let retType = snd $ NonEmpty.head cbrs'
  return (ConBranches (fst <$> cbrs'), retType)
inferBranches er (LitBranches lbrs def) = do
  lbrs' <- forM lbrs (\(l, br) -> (,) l . fst <$> infer er br)
  (def', typ) <- infer er def
  return (LitBranches lbrs' def', typ)

subtype :: ErasableM -> ErasableM -> TCM (ErasableM -> ErasableM)
subtype e1 e2 = do
  e1' <- whnf e1
  e2' <- whnf e2
  logErasable 30 "subtype e1" e1'
  logErasable 30 "subtype e2" e2'
  case (e1', e2') of
    _ | e1' == e2' -> return id
    (Pi h1 er1 argType1 retScope1, Pi h2 er2 argType2 retScope2) -> do
      let h = h1 <> h2
      f1 <- subtype argType2 argType1
      v2 <- forall h er2 argType2
      subErasability er2 er1
      let v1 = f1 $ pure v2
          retType1 = instantiate1 v1 retScope1
          retType2 = instantiate1 (pure v2) retScope2
      f2 <- subtype retType1 retType2
      return $ \x -> lam h er2 argType2 $ abstract1 v2 $ f2 $ app x er1 v1
    _ -> do unify e1' e2'; return id

unify :: ErasableM -> ErasableM -> TCM ()
unify expr1 expr2 = do
  expr1' <- whnf expr1
  expr2' <- whnf expr2
  case (expr1', expr2') of
    _ | expr1' == expr2' -> return ()
    (App e1 a1 e1', App e2 a2 e2') | a1 == a2 -> do
      unify e1  e2
      unify e1' e2'
    _ -> throwError
      $ "Can't unify types: "
      ++ show (pretty (show <$> expr1, show <$> expr2))

-------------------------------------------------------------------------------
-- Definitions
checkDataType
  :: PrettyAnnotation a
  => DataDef (Expr a) MetaVar
  -> ErasableM
  -> TCM (DataDef (Expr MetaErasability) MetaVar)
checkDataType (DataDef cs) typ = mdo

  vs <- forMTele (telescope typ) $ \h e s ->
    forall h e $ instantiateTele pure vs s

  cs' <- forM cs $ \(ConstrDef c s) -> do
    let t = instantiateTele pure vs s
    (t', _) <- infer MErased t
    return $ ConstrDef c $ abstract (teleAbstraction vs) t'

  return $ DataDef cs'

checkDefType
  :: PrettyAnnotation a
  => Definition (Expr a) MetaVar
  -> ErasableM
  -> TCM (Definition (Expr MetaErasability) MetaVar)
checkDefType (Definition e) typ = Definition <$> check MRetained e typ
checkDefType (DataDefinition d) typ = DataDefinition <$> checkDataType d typ

generaliseDefs
  :: Vector ( MetaVar
            , Definition (Expr MetaErasability) MetaVar
            )
  -> TCM (Vector ( Definition ExprE (Var Int MetaVar)
                 , Scope Int ExprE MetaVar
                 )
         )
generaliseDefs ds = do
  let types = (\(v, _) -> (v, metaType v)) <$> ds
  ds' <- traverse (bitraverse pure $ traverseDefinitionFirst (toErasability Erased)) ds
  types' <- traverse (bitraverse pure $ bitraverse (toErasability Erased) pure) types
  let abstractedDs = recursiveAbstractDefs ds'
      abstractedTypes = recursiveAbstract types'
  return $ Vector.zip abstractedDs abstractedTypes

inferRecursiveDefs
  :: PrettyAnnotation a
  => Vector ( Name
            , Definition (Expr a) (Var Int MetaVar)
            , Scope Int (Expr a) MetaVar
            )
  -> TCM (Vector ( Definition ExprE (Var Int MetaVar)
                 , Scope Int ExprE MetaVar
                 )
         )
inferRecursiveDefs ds = mdo
  evs <- Vector.forM ds $ \(v, _, t) -> do
    logPretty 20 "InferErasability.inferRecursiveDefs" v
    (t', _) <- inferType MErased $ instantiate (pure . (evs Vector.!)) t
    let h = fromName v
    forall h MRetained t'
  let instantiatedDs = flip Vector.map ds $ \(_, e, _) ->
        instantiateDef (pure . (evs Vector.!)) e

  results <- flip Vector.imapM instantiatedDs $ \i d -> do
    let v = evs Vector.! i
    d' <- checkDefType d $ metaType v
    return (v, d')

  generaliseDefs results
