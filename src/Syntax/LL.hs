{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts #-}
module Syntax.LL where

import qualified Bound.Scope.Simple as Simple
import Control.Monad
import Data.Bifunctor
import Data.Maybe
import Data.String
import Data.Hashable
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Prelude.Extras

import Syntax
import Util

data Lifted e v = Lifted (Vector (NameHint, Body Expr Tele)) (Simple.Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Body e v
  = Constant (e v)
  | Function (Vector NameHint) (Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type LBody = Lifted (Body Expr)

data Expr v
  = Var v
  | Global Name
  | Con Literal (Vector v) -- ^ fully applied
  | Ref (Expr v)
  | Let NameHint (Expr v) (Scope () Expr v)
  | Call v (Vector v)
  | KnownCall Name (Vector v)
  | Case v (Branches Literal Expr v)
  | Error
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-------------------------------------------------------------------------------
-- Smart constructors and related functionality
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
    f = (`Vector.elemIndex` fvs)

permuteVars :: Var a (Var b c) -> Var b (Var a c)
permuteVars = unvar (F . B) (unvar B (F . F))

letBody :: NameHint -> Expr v -> Body Expr (Var () v) -> Body Expr v
letBody h e (Constant e') = Constant $ letExpr h e (toScope e')
letBody h e (Function vs s) = Function vs $ toScope $ letExpr h (F <$> e) $ toScope $ permuteVars <$> fromScope s

letLifted :: (Eq v, Hashable v) => NameHint -> LBody v -> Simple.Scope () LBody v -> LBody v
letLifted h (Lifted ds1 (Simple.Scope b1)) (Simple.Scope (Lifted ds2 b2)) = do
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
                                               (unvar (const $ Call (B len) $ F <$> vs')  (pure . F))
    Constant e1 -> Lifted newContext $ Simple.Scope $ letBody h e1 $ permuteVars <$> b2'

letLifteds :: (Eq v, Hashable v) => Vector (NameHint, LBody v) -> Simple.Scope Int LBody v -> LBody v
letLifteds es s = unvar (error "LL.lets'") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go :: (Eq v, Hashable v) => (Int, (NameHint, LBody v)) -> LBody (Var Int v) -> LBody (Var Int v)
    go (n, (h, e)) e' = letLifted h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

bind :: Expr v -> (v -> LBody v') -> LBody v'
bind expr f = case expr of
  Var v -> f v
  Global n -> undefined -- constDef $ Global n
  Con l vs -> undefined

letExpr :: NameHint -> Expr v -> Scope1 Expr v -> Expr v
letExpr _ e (Scope (Var (B ()))) = e
letExpr _ (Var v) s = instantiate1 (pure v) s
letExpr _ (Global g) s = instantiate1 (Global g) s
letExpr h e s = Let h e s

letExprs :: Vector (NameHint, Expr v) -> Scope Int Expr v -> Expr v
letExprs es s = unvar (error "LL.letExprs") id <$> foldr go (fromScope s) (Vector.indexed es)
  where
    go :: (Int, (NameHint, Expr v)) -> Expr (Var Int v) -> Expr (Var Int v)
    go (n, (h, e)) e' = letExpr h (F <$> e) $ abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

call :: Expr v -> Vector (Expr v) -> Expr v
call (KnownCall g vs) es
  = letExprs ((,) mempty <$> es)
  $ Scope $ KnownCall g $ ((pure . pure) <$> vs) <> (B <$> Vector.enumFromN 0 (Vector.length es))
call (Call v vs) es
  = letExprs ((,) mempty <$> es)
  $ Scope $ Call ((pure . pure) v) $ ((pure . pure) <$> vs) <> (B <$> Vector.enumFromN 0 (Vector.length es))
call (Global g) es
  = letExprs ((,) mempty <$> es)
  $ Scope $ KnownCall g $ B <$> Vector.enumFromN 0 (Vector.length es)
call e es
  = letExprs ((,) mempty <$> Vector.cons e es)
  $ Scope $ Call (B 0) $ B <$> Vector.enumFromN 1 (Vector.length es)

con :: Literal -> Vector (Expr v) -> Expr v
con l es
  = letExprs ((,) mempty <$> es)
  $ Scope $ Con l $ B <$> Vector.enumFromN 0 (Vector.length es)

case_ :: Expr v -> Branches Literal Expr v -> Expr v
case_ e brs = letExpr mempty e $ Scope $ Case (B ()) $ F . pure <$> brs

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

instance Monad Expr where
  return = Var
  Var v >>= f = f v
  Global g >>= _ = Global g
  Con l vs >>= f = con l $ f <$> vs
  Ref e >>= f = Ref (e >>= f)
  Let h e s >>= f = letExpr h (e >>= f) (s >>>= f)
  Call v vs >>= f = call (f v) (f <$> vs)
  KnownCall g vs >>= f = call (Global g) (f <$> vs)
  Case v brs >>= f = case_ (f v) (brs >>>= f)
  Error >>= _ = Error

instance (Eq v, IsString v, Pretty v, Pretty (e v), Monad e)
      => Pretty (Lifted e v) where
  prettyM (Lifted ds s) = withNameHints (fst <$> ds) $ \ns ->
    prettyM (Simple.instantiate (pure . fromText . (ns Vector.!) . unTele) s) <$$>
      prettyM "where" <$$>
        indent 2 (vcat (Vector.toList $ (prettyM . fmap ((ns Vector.!) . unTele) . snd) <$> ds))

instance (Eq v, IsString v, Pretty v, Pretty (e v), Monad e)
      => Pretty (Body e v) where
  prettyM body = case body of
    Constant e -> prettyM e
    Function hs s -> withNameHints hs $ \ns ->
      prettyM "\\" <> hsep (map prettyM $ Vector.toList ns) <> prettyM "." <+>
        associate absPrec (prettyM $ instantiate (pure . fromText . (ns Vector.!) . unTele) s)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Var v -> prettyM v
    Global g -> prettyM g
    Con c vs -> prettyApps (prettyM c) (prettyM <$> vs)
    Ref e -> prettyApp (prettyM "Ref") $ prettyM e
    Let h e s -> parens `above` letPrec $
      withNameHint h $ \n ->
        prettyM "let" <+> prettyM n <+> prettyM ":" <+> inviolable (prettyM e) <+> prettyM "in" <$$>
        prettyM (instantiate1 (pure $ fromText n) s)
    Call v vs -> prettyApps (prettyM v) (prettyM <$> vs)
    KnownCall v vs -> prettyApps (prettyM v) (prettyM <$> vs)
    Case v brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM v) <+> prettyM "of" <$$> indent 2 (prettyM brs)
    Error  -> prettyM "ERROR"
