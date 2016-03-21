{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, Rank2Types, ViewPatterns #-}
module Syntax.LL where

import qualified Bound.Scope.Simple as Simple
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import Data.Maybe
import Data.String
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Context
import Syntax
import Util

data Lifted e v = Lifted (Vector (NameHint, Body Expr Tele)) (Simple.Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Body e v
  = Constant (e v)
  | Function (Vector NameHint) (Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type LBody = Lifted (Body Expr)
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

-------------------------------------------------------------------------------
-- Smart constructors and related functionality
mapLifted
  :: (e (Var Tele v) -> e' (Var Tele v'))
  -> Lifted e v
  -> Lifted e' v'
mapLifted f (Lifted vs (Simple.Scope s)) = Lifted vs $ Simple.Scope $ f s

operandView :: Expr v -> Maybe (Operand v)
operandView (Operand v) = Just v
operandView _ = Nothing

pureLifted :: Functor e => e v -> Lifted e v
pureLifted = Lifted mempty . Simple.Scope . fmap F

constantLifted :: Functor e => e v -> Lifted (Body e) v
constantLifted = pureLifted . Constant

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

permuteVars :: Var a (Var b c) -> Var b (Var a c)
permuteVars = unvar (F . B) (unvar B (F . F))

letLifted
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> t Expr (Var () a) -> t Expr a)
  -> NameHint
  -> LBody v
  -> Simple.Scope () (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLifted k h (Lifted ds1 (Simple.Scope b1)) (Simple.Scope (Lifted ds2 b2)) = do
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
    Constant e1 -> Lifted newContext $ Simple.Scope $ (k h) e1 $ permuteVars <$> b2'

letLifteds
  :: (Eq v, Functor (t Expr), Bound t, Hashable v)
  => (forall a. NameHint -> Expr a -> t Expr (Var () a) -> t Expr a)
  -> Vector (NameHint, LBody v)
  -> Simple.Scope Int (Lifted (t Expr)) v
  -> Lifted (t Expr) v
letLifteds k es s = unvar (error "LL.lets'") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLifted k h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

caseLifted
  :: (Eq v, Hashable v)
  => LBody v
  -> LBranches v
  -> LBody v
caseLifted b brs
  = letLifted letBody mempty b
  $ Simple.Scope
  $ mapLifted (Constant . Case (Local $ F $ B ()) . fmap (fmap F))
  $ brs

newtype ExposedConBranches b v
  = ExposedConBranches [(QConstr, Vector (NameHint, Annotation), b v)]
  deriving (Functor)

instance Bound ExposedConBranches where
  ExposedConBranches brs >>>= f
    = ExposedConBranches [(qc, hs, br >>= f) | (qc, hs, br) <- brs]

bindExposedConBranches
  :: ExposedConBranches Expr (Var Tele v)
  -> Expr v
  -> Branches QConstr Expr v
bindExposedConBranches (ExposedConBranches brs) typ
  = ConBranches [(qc, hs, toScope b) | (qc, hs, b) <- brs] typ

conBranchesLifted
  :: (Eq v, Hashable v)
  => [(QConstr, Vector (NameHint, Annotation), LBody (Var Tele v))]
  -> Expr v
  -> LBranches v
conBranchesLifted brs typ
  = mapLifted (flip bindExposedConBranches (F <$> typ) . fmap commute)
  $ letLifteds (\_ e b -> b >>>= unvar (\() -> e) pure)
               (Vector.fromList [(mempty, br) | (_, _, br) <- brs])
               (Simple.Scope $ pureLifted $ ExposedConBranches [(c, hs, pure $ B n) | ((c, hs, _), n) <- zip brs [0..]])

litBranchesLifted
  :: (Eq v, Hashable v)
  => [(Literal, LBody v)]
  -> LBody v
  -> LBranches v
litBranchesLifted brs def
  = letLifteds (\_ e b -> b >>>= unvar (\() -> e) pure)
  (Vector.fromList $ pure (mempty, def) <> (first (const mempty) <$> brs))
  (Simple.Scope $ pureLifted $ LitBranches [(l, pure $ B n) | ((l, _), n) <- zip brs [1..]] (pure $ B 0))

lamLifted :: Vector NameHint -> LBody (Var Tele v) -> LBody v
lamLifted hs (Lifted bs (Simple.Scope (Constant expr)))
  = Lifted bs
  $ Simple.Scope
  $ Function hs
  $ toScope
  $ commute <$> expr
lamLifted hs (Lifted bs (Simple.Scope (Function hs' expr)))
  = Lifted bs
  $ Simple.Scope
  $ Function (hs <> hs')
  $ toScope
  $ fmap (unvar (B . (+ Tele (Vector.length hs))) (unvar B F))
  $ fromScope
  $ commute <$> expr

commute :: Var a (Var b c) -> Var b (Var a c)
commute = unvar (F . B) (unvar B (F . F))

callLifted
  :: (Eq v, Hashable v)
  => LBody v
  -> Vector (LBody v)
  -> LBody v
callLifted fun args
  = letLifteds letBody ((,) mempty <$> pure fun <> args)
  $ Simple.Scope $ constantLifted
  $ Call (Local $ B 0) $ Local . B <$> Vector.enumFromN 1 (Vector.length args)

conLifted
  :: (MonadError String cxt, Context cxt, Eq v, Hashable v, Monad (ContextExpr cxt), Syntax (ContextExpr cxt))
  => QConstr
  -> Vector (LBody v)
  -> cxt (LBody v)
conLifted qc args = do
  n <- Context.relevantArity qc
  let argsLen = Vector.length args
  case compare argsLen n of
    LT -> return $ letLifteds letBody ((,) mempty <$> args)
        $ Simple.Scope $ pureLifted
        $ Function (Vector.replicate (n - argsLen) mempty)
        $ toScope $ Con qc
        $ (Local . F . B <$> Vector.enumFromN 0 argsLen)
           <> (Local . B <$> Vector.enumFromN 0 ((n - argsLen) `max` 0))
    EQ -> return $ letLifteds letBody ((,) mempty <$> args) $ Simple.Scope
        $ constantLifted $ Con qc $ Local . B <$> Vector.enumFromN 0 n
    GT -> throwError $ "conLifted: too many args to constructor: " ++ show qc

letBody :: NameHint -> Expr v -> Body Expr (Var () v) -> Body Expr v
letBody h e (Constant e') = Constant $ letExpr h e (toScope e')
letBody h e (Function vs s) = Function vs $ toScope $ letExpr h (F <$> e) $ toScope $ permuteVars <$> fromScope s

letExpr :: NameHint -> Expr v -> Scope1 Expr v -> Expr v
letExpr _ e (Scope (Operand (Local (B ())))) = e
letExpr _ (Operand v) s = instantiate1 (Operand v) s
letExpr h e s = Let h e s

instantiateBody :: (b -> Expr v) -> Body Expr (Var b v) -> Body Expr v
instantiateBody f (Constant e') = Constant $ instantiate f (toScope e')
instantiateBody f (Function vs s) = Function vs $ toScope $ instantiate (fmap F <$> f) $ toScope $ permuteVars <$> fromScope s

instantiate1Body :: Expr v -> Body Expr (Var () v) -> Body Expr v
instantiate1Body e = instantiateBody (\() -> e)

letExprs :: Vector (NameHint, Expr v) -> Scope Int Expr v -> Expr v
letExprs es s = unvar (error "LL.letExprs") id <$> foldr go (fromScope s) (Vector.indexed es)
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
