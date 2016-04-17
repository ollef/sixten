{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, ViewPatterns #-}
module Syntax.Lifted where

import qualified Bound.Scope.Simple as Simple
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.Maybe
import Data.String
import Data.Foldable
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void
import Prelude.Extras

import Syntax
import TCM
import Util

data Lifted e v = Lifted (Vector (NameHint, Body Expr Tele)) (Simple.Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Body e v
  = Constant (e v)
  | Function (Vector NameHint) (Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance (Show1 e, Functor e) => Show1 (Body e) where
  showsPrec1 d (Constant e) = showParen (d > 10) $
    showString "Constant " . showsPrec1 11 e
  showsPrec1 d (Function xs s) = showParen (d > 10) $
    showString "Function " . showsPrec 11 xs . showString " " . showsPrec 11 s

type LBody = Lifted (Body Expr)
type LExpr = Lifted Expr
type LBranches = Lifted (Branches QConstr Expr)

data Operand v
  = Local v
  | Global Name
  | Lit Literal
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Expr v
  = Operand (Operand v)
  | Con QConstr (Vector (Operand v)) -- ^ fully applied
  | Ref (Expr v)
  | Let NameHint (Expr v) (Scope () Expr v)
  | Call (Operand v) (Vector (Operand v))
  | Case (Operand v) (Branches QConstr Expr v)
  | Error
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

pureLifted :: Functor e => e v -> Lifted e v
pureLifted = Lifted mempty . Simple.Scope . fmap F

singleLifted
  :: Functor e
  => NameHint
  -> Body Expr Void
  -> Simple.Scope () e v
  -> Lifted e v
singleLifted h b s = Lifted (pure (h, vacuous b)) $ Simple.mapBound (\() -> Tele 0) s

mapLifted
  :: (e (Var Tele v) -> e' (Var Tele v'))
  -> Lifted e v
  -> Lifted e' v'
mapLifted f (Lifted vs (Simple.Scope s)) = Lifted vs $ Simple.Scope $ f s

-------------------------------------------------------------------------------
-- Views
operandView :: Expr v -> Maybe (Operand v)
operandView (Operand v) = Just v
operandView _ = Nothing

newtype IdentityBound b v = IdentityBound { unIdentityBound :: b v }
  deriving (Functor)

instance Bound IdentityBound where
  IdentityBound x >>>= f = IdentityBound $ x >>= f

newtype ExposedConBranches b v
  = ExposedConBranches [(QConstr, Vector (NameHint, Annotation, b v), b v)]
  deriving (Functor)

instance Bound ExposedConBranches where
  ExposedConBranches brs >>>= f
    = ExposedConBranches [ (qc, (\(h, a, t) -> (h, a, t >>= f)) <$> tele, br >>= f)
                         | (qc, tele, br) <- brs]

bindExposedConBranches
  :: ExposedConBranches Expr (Var Tele v)
  -> Expr v
  -> Branches QConstr Expr v
bindExposedConBranches (ExposedConBranches brs)
  = ConBranches [ (qc, Telescope $ (\(h, a, t) -> (h, a, toScope t)) <$> tele, toScope b)
                | (qc, tele, b) <- brs]

-------------------------------------------------------------------------------
-- Exprs
letExpr :: NameHint -> Expr v -> Scope1 Expr v -> Expr v
letExpr _ e (Scope (Operand (Local (B ())))) = e
letExpr _ (Operand v) s = instantiate1 (Operand v) s
letExpr h e s = Let h e s

letExprs :: Vector (NameHint, Expr v) -> Scope Int Expr v -> Expr v
letExprs es s = unvar (error "Lifted.letExprs") id <$> foldr go (fromScope s) (Vector.indexed es)
  where
    go :: (Int, (NameHint, Expr v)) -> Expr (Var Int v) -> Expr (Var Int v)
    go (n, (h, e)) e' = letExpr h (F <$> e) $ abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

callExpr :: Expr v -> Vector (Expr v) -> Expr v
callExpr (Operand v) (mapM operandView -> Just vs) = Call v vs
callExpr (Call v vs) (mapM operandView -> Just vs') = Call v $ vs <> vs'
callExpr e es
  = letExprs ((,) mempty <$> Vector.cons e es)
  $ Scope $ Call (Local $ B 0) $ Local . B <$> Vector.enumFromN 1 (Vector.length es)

conExpr :: QConstr -> Vector (Expr v) -> Expr v
conExpr qc (mapM operandView -> Just vs) = Con qc vs
conExpr qc es
  = letExprs ((,) mempty <$> es)
  $ Scope $ Con qc $ Local . B <$> Vector.enumFromN 0 (Vector.length es)

caseExpr :: Expr v -> Branches QConstr Expr v -> Expr v
caseExpr (Operand v) brs = Case v brs
caseExpr e brs = letExpr mempty e $ Scope $ Case (Local $ B ()) $ F . pure <$> brs

-------------------------------------------------------------------------------
-- Lifted Exprs
-- TODO reduce duplication between these and then functions on bodies?
letLExpr'
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> Simple.Scope () (t Expr) a -> t Expr a)
  -> NameHint
  -> LExpr v
  -> Simple.Scope () (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLExpr' k h e = letLBody k' h $ mapLifted Constant e
  where
    k' h' e' texpr = k h' e' $ Simple.Scope texpr

letLExprs'
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> Simple.Scope () (t Expr) a -> t Expr a)
  -> Vector (NameHint, LExpr v)
  -> Simple.Scope Int (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLExprs' k es s = unvar (error "Lifted.letLExprs'") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLExpr' k h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

letLExpr
  :: (Eq v, Hashable v)
  => (forall a. NameHint -> Expr a -> Scope1 Expr a -> Expr a)
  -> NameHint
  -> LExpr v
  -> Simple.Scope () (Lifted Expr) v
  -> Lifted Expr v
letLExpr k hint expr s = mapLifted unIdentityBound $ letLExpr' k' hint expr s'
  where
    k' h e e' = IdentityBound $ k h e (toScope $ unIdentityBound $ Simple.fromScope e')
    s' = Simple.hoistScope (mapLifted IdentityBound) s

letLExprs
  :: (Eq v, Hashable v)
  => (forall a. NameHint -> Expr a -> Scope1 Expr a -> Expr a)
  -> Vector (NameHint, LExpr v)
  -> Simple.Scope Int (Lifted Expr) v
  -> Lifted Expr v
letLExprs k es s = unvar (error "Lifted.letLExprs") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLExpr k h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

caseLExpr
  :: (Eq v, Hashable v)
  => LExpr v
  -> LBranches v
  -> LExpr v
caseLExpr b brs
  = letLExpr letExpr mempty b
  $ Simple.Scope
  $ mapLifted (Case (Local $ F $ B ()) . fmap (fmap F)) brs

conLExprBranches
  :: (Eq v, Hashable v)
  => [(QConstr, Vector (NameHint, Annotation, LExpr (Var Tele v)), LExpr (Var Tele v))]
  -> Expr v
  -> LBranches v
conLExprBranches brs typ
  = mapLifted (flip bindExposedConBranches (F <$> typ) . fmap commuteVars)
  $ letLExprs'
    (\_ e (Simple.Scope b) -> b >>>= unvar (\() -> e) pure)
    (Vector.fromList [(mempty, br) | (_, _, br) <- brs]
    <> Vector.concat [(\(h, _, e) -> (h, e)) <$> tele | (_, tele, _) <- brs])
  $ Simple.Scope
  $ pureLifted
  $ ExposedConBranches [(c, (\((h, a, _), t) -> (h, a, t)) <$> tele, pure $ B n) | ((c, tele), n) <- zip numberedBrs [0..]]
  where
    numberedBrs = reverse $ fst $ foldl'
      (\(brs', n) (c, tele, _) ->
        let len = Vector.length tele in
        ((c, Vector.zip tele $ pure . B <$> Vector.enumFromN n len) : brs', n + len)
      )
      ([], length brs)
      brs

litLExprBranches
  :: (Eq v, Hashable v)
  => [(Literal, LExpr v)]
  -> LExpr v
  -> LBranches v
litLExprBranches brs def
  = letLExprs' (\_ e (Simple.Scope b) -> b >>>= unvar (\() -> e) pure)
  (Vector.fromList $ pure (mempty, def) <> (first (const mempty) <$> brs))
  (Simple.Scope $ pureLifted $ LitBranches [(l, pure $ B n) | ((l, _), n) <- zip brs [1..]] (pure $ B 0))

conLExpr :: (Eq v, Hashable v) => QConstr -> Vector (LExpr v) -> TCM s (LExpr v)
conLExpr qc args = do
  n <- relevantConstrArity qc
  let argsLen = Vector.length args
  when (argsLen /= n) $ throwError "Lifted.conLExpr: Wrong number of constructor arguments"
  return $ letLExprs letExpr ((,) mempty <$> args) $ Simple.Scope
         $ pureLifted $ Con qc $ Local . B <$> Vector.enumFromN 0 n

-------------------------------------------------------------------------------
-- Bodies
letBody :: NameHint -> Expr v -> Body Expr (Var () v) -> Body Expr v
letBody h e (Constant e') = Constant $ letExpr h e (toScope e')
letBody h e (Function vs s) = Function vs $ toScope $ letExpr h (F <$> e) $ toScope $ commuteVars <$> fromScope s

instantiateBody :: (b -> Expr v) -> Body Expr (Var b v) -> Body Expr v
instantiateBody f (Constant e') = Constant $ instantiate f (toScope e')
instantiateBody f (Function vs s) = Function vs $ toScope $ instantiate (fmap F <$> f) $ toScope $ commuteVars <$> fromScope s

instantiate1Body :: Expr v -> Body Expr (Var () v) -> Body Expr v
instantiate1Body e = instantiateBody (\() -> e)

-------------------------------------------------------------------------------
-- Lifted Bodies
constantLBody :: Functor e => e v -> Lifted (Body e) v
constantLBody = pureLifted . Constant

liftFunction
  :: (Eq f, Hashable f)
  => Vector NameHint
  -> Scope Tele Expr (Var b f)
  -> (Body Expr b, Vector f)
liftFunction vs s =
  ( Function (fmap mempty fvs <> vs)
    $ toScope
    $ unvar (B . (+ Tele fvsLen)) (unvar F $ fromJust err . ix)
   <$> fromScope s
  , fvs
  )
  where
    ix = Tele . fromJust err . (`Vector.elemIndex` fvs)
    err = error "liftFunction"
    fvs = Vector.fromList $ HashSet.toList $ toHashSet $ Simple.Scope s
    fvsLen = Vector.length fvs

commuteVars :: Var a (Var b c) -> Var b (Var a c)
commuteVars = unvar (F . B) (unvar B (F . F))

letLBody
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> t Expr (Var () a) -> t Expr a)
  -> NameHint
  -> LBody v
  -> Simple.Scope () (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLBody k h (Lifted ds1 (Simple.Scope b1)) (Simple.Scope (Lifted ds2 b2)) = do
  let newContext = ds1 <> ds2'
      len = Tele $ Vector.length newContext
      (f, fScope) | Vector.null ds1 = (id, id)
                  | otherwise = let fun = (+ Tele (Vector.length ds1)) in (fmap fun, Simple.mapBound fun)
      ds2' = second f <$> ds2
      b2' = Simple.fromScope $ fScope b2
  case b1 of
    Function vs s -> do
      let (function', vs') = liftFunction vs s
      Lifted (newContext <> pure (h, function'))
             $ Simple.toScope $ b2' >>>= unvar (pure . B)
                                               (unvar (const $ Call (Local $ B len) $ Local . F <$> vs')  (pure . F))
    Constant e1 -> Lifted newContext $ Simple.Scope $ k h e1 $ commuteVars <$> b2'

letLBodies
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> t Expr (Var () a) -> t Expr a)
  -> Vector (NameHint, LBody v)
  -> Simple.Scope Int (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLBodies k es s = unvar (error "Lifted.letLBodies") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLBody k h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

caseLBody
  :: (Eq v, Hashable v)
  => LBody v
  -> LBranches v
  -> LBody v
caseLBody b brs
  = letLBody letBody mempty b
  $ Simple.Scope
  $ mapLifted (Constant . Case (Local $ F $ B ()) . fmap (fmap F)) brs

conLBodyBranches
  :: (Eq v, Hashable v)
  => [(QConstr, Vector (NameHint, Annotation, LBody (Var Tele v)), LBody (Var Tele v))]
  -> Expr v
  -> LBranches v
conLBodyBranches brs typ
  = mapLifted (flip bindExposedConBranches (F <$> typ) . fmap commuteVars)
  $ letLBodies
    (\_ e b -> b >>>= unvar (\() -> e) pure)
    (Vector.fromList [(mempty, br) | (_, _, br) <- brs]
    <> Vector.concat [(\(h, _, e) -> (h, e)) <$> tele | (_, tele, _) <- brs])
  $ Simple.Scope
  $ pureLifted
  $ ExposedConBranches [(c, (\((h, a, _), t) -> (h, a, t)) <$> tele, pure $ B n) | ((c, tele), n) <- zip numberedBrs [0..]]
  where
    numberedBrs = reverse $ fst $ foldl'
      (\(brs', n) (c, tele, _) ->
        let len = Vector.length tele in
        ((c, Vector.zip tele $ pure . B <$> Vector.enumFromN n len) : brs', n + len)
      )
      ([], length brs)
      brs

litLBodyBranches
  :: (Eq v, Hashable v)
  => [(Literal, LBody v)]
  -> LBody v
  -> LBranches v
litLBodyBranches brs def
  = letLBodies (\_ e b -> b >>>= unvar (\() -> e) pure)
  (Vector.fromList $ pure (mempty, def) <> (first (const mempty) <$> brs))
  (Simple.Scope $ pureLifted $ LitBranches [(l, pure $ B n) | ((l, _), n) <- zip brs [1..]] (pure $ B 0))

lamLBody :: Vector NameHint -> LBody (Var Tele v) -> LBody v
lamLBody hs (Lifted bs (Simple.Scope (Constant expr)))
  = Lifted bs
  $ Simple.Scope
  $ Function hs
  $ toScope
  $ commuteVars <$> expr
lamLBody hs (Lifted bs (Simple.Scope (Function hs' expr)))
  = Lifted bs
  $ Simple.Scope
  $ Function (hs <> hs')
  $ toScope
  $ fmap (unvar (B . (+ Tele (Vector.length hs))) (unvar B F))
  $ fromScope
  $ commuteVars <$> expr

callLBody
  :: (Eq v, Hashable v)
  => LBody v
  -> Vector (LBody v)
  -> LBody v
callLBody fun args
  = letLBodies letBody ((,) mempty <$> pure fun <> args)
  $ Simple.Scope $ constantLBody
  $ Call (Local $ B 0) $ Local . B <$> Vector.enumFromN 1 (Vector.length args)

conLBody
  :: (Eq v, Hashable v)
  => QConstr
  -> Vector (LBody v)
  -> TCM s (LBody v)
conLBody qc args = do
  n <- relevantConstrArity qc
  let argsLen = Vector.length args
  case compare argsLen n of
    LT -> return $ letLBodies letBody ((,) mempty <$> args)
        $ Simple.Scope $ pureLifted
        $ Function (Vector.replicate (n - argsLen) mempty)
        $ toScope $ Con qc
        $ (Local . F . B <$> Vector.enumFromN 0 argsLen)
           <> (Local . B <$> Vector.enumFromN 0 ((n - argsLen) `max` 0))
    EQ -> return $ letLBodies letBody ((,) mempty <$> args) $ Simple.Scope
        $ constantLBody $ Con qc $ Local . B <$> Vector.enumFromN 0 n
    GT -> throwError $ "Lifted.conLBody: too many args to constructor: " ++ show qc

-------------------------------------------------------------------------------
-- Instances
instance Bound Lifted where
  Lifted ds d >>>= f = Lifted ds (d >>>= f)

instance Bound Body where
  Function vs s >>>= f = Function vs $ s >>>= f
  Constant e >>>= f = Constant $ e >>= f

instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance Applicative Expr where
  pure = return
  (<*>) = ap

bindOperand :: (v -> Expr v') -> Operand v -> Expr v'
bindOperand f (Local v) = f v
bindOperand _ (Global g) = Operand $ Global g
bindOperand _ (Lit l) = Operand $ Lit l

instance Monad Expr where
  return = Operand . Local
  Operand v >>= f = bindOperand f v
  Con c vs >>= f = conExpr c $ bindOperand f <$> vs
  Ref e >>= f = Ref (e >>= f)
  Let h e s >>= f = letExpr h (e >>= f) (s >>>= f)
  Call v vs >>= f = callExpr (bindOperand f v) (bindOperand f <$> vs)
  Case v brs >>= f = caseExpr (bindOperand f v) (brs >>>= f)
  Error >>= _ = Error

instance (Eq v, IsString v, Pretty v, Pretty (e v), Functor e)
      => Pretty (Lifted e v) where
  prettyM (Lifted ds (Simple.Scope s)) = withNameHints (fst <$> ds) $ \ns ->
    let toName = fromText . (ns Vector.!) . unTele
        addWheres x | Vector.null ds = x
        addWheres x = x <$$> indent 2 (prettyM "where" <$$>
          indent 2 (vcat $ Vector.toList $ (\(n, (_, e)) -> prettyM n <+> prettyM "=" <+> prettyM (toName <$> e)) <$> Vector.zip ns ds))
     in addWheres $ prettyM (unvar toName id <$> s)

instance (Eq v, IsString v, Pretty v, Pretty (e v), Monad e)
      => Pretty (Body e v) where
  prettyM body = case body of
    Constant e -> prettyM e
    Function hs s -> withNameHints hs $ \ns ->
      prettyM "\\" <> hsep (map prettyM $ Vector.toList ns) <> prettyM "." <+>
        associate absPrec (prettyM $ instantiate (pure . fromText . (ns Vector.!) . unTele) s)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Operand v) where
  prettyM (Local v) = prettyM v
  prettyM (Global g) = prettyM g
  prettyM (Lit l) = prettyM l

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Operand v -> prettyM v
    Con c vs -> prettyApps (prettyM c) (prettyM <$> vs)
    Ref e -> prettyApp (prettyM "Ref") $ prettyM e
    Let h e s -> parens `above` letPrec $
      withNameHint h $ \n ->
        prettyM "let" <+> prettyM n <+> prettyM "=" <+> inviolable (prettyM e) <+> prettyM "in" <$$>
          indent 2 (inviolable $ prettyM $ instantiate1 (pure $ fromText n) s)
    Call v vs -> prettyApps (prettyM v) (prettyM <$> vs)
    Case v brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM v) <+> prettyM "of" <$$> indent 2 (prettyM brs)
    Error  -> prettyM "ERROR"
