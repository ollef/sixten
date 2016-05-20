{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, Rank2Types, ViewPatterns #-}
module Syntax.Lifted where

import GHC.Generics(Generic)
import qualified Bound.Scope.Simple as Simple
import Control.Monad
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
import Util

data Lifted e v = Lifted (Vector (NameHint, Body Tele)) (Simple.Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Body v
  = Constant (Expr v)
  | Function (Vector NameHint) (Simple.Scope Tele Expr v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type LBody = Lifted Body
type LExpr = Lifted Expr
type LBranches = Lifted (SimpleBranches QConstr Expr)

data Operand v
  = Local v
  | Global Name
  | Lit Literal
  deriving (Eq, Ord, Show, Functor, Foldable, Generic, Traversable)

instantiateOperand
  :: BindOperand f
  => (b -> Operand a)
  -> Simple.Scope b f a -> f a
instantiateOperand f (Simple.Scope s) = bindOperand (unvar f pure) s

instance Hashable v => Hashable (Operand v)

instance IsString v => IsString (Operand v) where
  fromString = Local . fromString

data Expr v
  = Sized (Operand v) (InnerExpr v)
  | Let NameHint (Expr v) (Simple.Scope () Expr v)
  | Case (Operand v, Operand v) (SimpleBranches QConstr Expr v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data InnerExpr v
  = Operand (Operand v)
  | Con QConstr (Vector (Operand v, Operand v)) -- ^ fully applied
  | Call (Operand v) (Vector (Operand v))
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

pureLifted :: Functor e => e v -> Lifted e v
pureLifted = Lifted mempty . Simple.Scope . fmap F

mapLifted
  :: (forall b. e (Var b v) -> e' (Var b v'))
  -> Lifted e v
  -> Lifted e' v'
mapLifted f (Lifted vs (Simple.Scope s)) = Lifted vs $ Simple.Scope $ f s

mapLifted'
  :: (e (Var Tele v) -> e' (Var Tele v'))
  -> Lifted e v
  -> Lifted e' v'
mapLifted' f (Lifted vs (Simple.Scope s)) = Lifted vs $ Simple.Scope $ f s

newtype VectorT a v = VectorT { unVectorT :: Vector (a v) }
  deriving (Functor)

-- ~sequence
liftVector
  :: Functor e
  => Vector (Lifted e v)
  -> Lifted (VectorT e) v
liftVector
  = uncurry Lifted
  . bimap Vector.concat
          (Simple.Scope . VectorT . fmap Simple.fromScope . Vector.fromList . reverse)
  . unzip
  . snd
  . foldl' go (0, mempty)
  where
    go (n, xs) (Lifted ls e)
      = ( n + Tele (Vector.length ls)
        , (second (fmap (+ n)) <$> ls, Simple.mapBound (+ n) e) : xs
        )

bindLiftedVector
  :: (Functor e, Functor e')
  => Vector (Lifted e v)
  -> (forall b. Vector (e (Var b v)) -> Lifted e' (Var b v'))
  -> Lifted e' v'
bindLiftedVector vs k = bindLifted (liftVector vs) (k . unVectorT)

data TupleT a b v = TupleT
  { fstT :: a v
  , sndT :: b v
  } deriving (Functor)

joinLifted
  :: Functor e
  => Lifted (Lifted e) v
  -> Lifted e v
joinLifted (Lifted es (Simple.Scope (Lifted es' (Simple.Scope e))))
  = Lifted (es <> es')
  $ Simple.Scope
  $ unvar (B . (+ len)) id <$> e
  where len = Tele $ Vector.length es

bindLifted
  :: Functor f
  => Lifted e a
  -> (forall v. e (Var v a) -> Lifted f (Var v b))
  -> Lifted f b
bindLifted x f = joinLifted $ mapLifted f x

bindLifted'
  :: Functor f
  => Lifted e a
  -> (e (Var Tele a) -> Lifted f (Var Tele b))
  -> Lifted f b
bindLifted' x f = joinLifted $ mapLifted' f x

singleLifted
  :: Functor e
  => NameHint
  -> Body Void
  -> Simple.Scope () e v
  -> Lifted e v
singleLifted h b s = Lifted (pure (h, vacuous b)) $ Simple.mapBound (\() -> Tele 0) s

-------------------------------------------------------------------------------
-- Exprs
letExpr :: NameHint -> Expr v -> Simple.Scope () Expr v -> Expr v
letExpr _ e (Simple.Scope (Sized _ (Operand (Local (B ()))))) = e
letExpr _ (Sized _ (Operand o)) s = instantiateOperand (\() -> o) s
letExpr h e s = Let h e s

letExprs :: Vector (NameHint, Expr v) -> Simple.Scope Int Expr v -> Expr v
letExprs es s = unvar (error "Lifted.letExprs") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go :: (Int, (NameHint, Expr v)) -> Expr (Var Int v) -> Expr (Var Int v)
    go (n, (h, e)) e' = letExpr h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

callExpr :: Expr v -> Expr v -> Vector (Expr v) -> Expr v
callExpr sz e es
  = letExprs ((,) mempty <$> Vector.cons sz (Vector.cons e es))
  $ Simple.Scope
  $ Sized (pure $ B 0)
  $ Call (pure $ B 1) $ pure . B <$> Vector.enumFromN 2 (Vector.length es)

conExpr :: Expr v -> QConstr -> Vector (Expr v, Expr v) -> Expr v
conExpr sz qc (Vector.unzip -> (es, szs))
  = letExprs ((,) mempty <$> Vector.cons sz (es <> szs))
  $ Simple.Scope $ Sized (pure $ B 0)
  $ Con qc $ Vector.zip (pure . B <$> Vector.enumFromN 1 len)
                        (pure . B <$> Vector.enumFromN (len + 1) len)
  where
    len = Vector.length es

caseExpr :: (Expr v, Expr v) -> SimpleBranches QConstr Expr v -> Expr v
caseExpr (e, esz) brs
  = letExprs ((,) mempty <$> Vector.fromList [e, esz])
  $ Simple.Scope $ Case (pure $ B 0, pure $ B 1) $ F <$> brs

-------------------------------------------------------------------------------
-- Lifted Exprs
letLExpr
  :: (Eq v, Hashable v)
  => NameHint
  -> LExpr v
  -> Simple.Scope () LExpr v
  -> LExpr v
letLExpr h lexpr (Simple.Scope lexpr')
  = bindLifted lexpr
  $ \expr -> bindLifted lexpr'
  $ \expr' -> pureLifted
  $ letExpr h (F <$> expr)
  $ Simple.Scope $ fmap (fmap F) . commuteVars <$> expr'

commuteVars :: Var a (Var b c) -> Var b (Var a c)
commuteVars = unvar (F . B) (unvar B (F . F))

letLExprs
  :: (Eq v, Hashable v)
  => Vector (NameHint, LExpr v)
  -> Simple.Scope Int LExpr v
  -> LExpr v
letLExprs es s = unvar (error "Lifted.letLExprs") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLExpr h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

caseLExpr
  :: (Eq v, Hashable v)
  => (LExpr v, LExpr v)
  -> LBranches v
  -> LExpr v
caseLExpr (b, bsz) brs
  = letLExprs ((,) mempty <$> Vector.fromList [b, bsz])
  $ Simple.Scope
  $ mapLifted (Case (pure $ F $ B 0, pure $ F $ B 1) . fmap (fmap F)) brs

conLExprBranches
  :: (Eq v, Hashable v)
  => [(QConstr, Vector (NameHint, Simple.Scope Tele LExpr v), Simple.Scope Tele LExpr v)]
  -> LBranches v
conLExprBranches brs
  = bindLiftedVector (Vector.fromList $ do
      (_, les, Simple.Scope le) <- brs
      return $
        bindLifted le $ \e -> bindLiftedVector (Simple.fromScope . snd <$> les) $ \es ->
          pureLifted $ TupleT (F <$> e) (fmap F <$> VectorT es)
      ) $ \ess ->
    pureLifted $ SimpleConBranches $ do
      ((qc, hes, _), TupleT e es) <- zip brs $ Vector.toList $ fmap commuteVars <$> ess
      let es' = Simple.Scope <$> unVectorT es
          hes' = Vector.zip (fst <$> hes) es'
      return (qc, SimpleTelescope hes', Simple.Scope e)

litLExprBranches
  :: (Eq v, Hashable v)
  => [(Literal, LExpr v)]
  -> LExpr v
  -> LBranches v
litLExprBranches lbrs ldef
  = bindLifted ldef
  $ \def -> bindLiftedVector (Vector.fromList $ snd <$> lbrs)
  $ \brs -> pureLifted
  $ SimpleLitBranches (zip (fst <$> lbrs) $ Vector.toList $ fmap (fmap F) <$> brs) (F <$> def)

conLExpr
  :: (Eq v, Hashable v)
  => LExpr v
  -> QConstr
  -> Vector (LExpr v, LExpr v)
  -> LExpr v
conLExpr sz qc (Vector.unzip -> (es, szs))
  = letLExprs ((,) mempty <$> Vector.cons sz (es <> szs)) $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B 0)
  $ Con qc $ Vector.zip (pure . B <$> Vector.enumFromN 1 len)
                        (pure . B <$> Vector.enumFromN (len + 1) len)
  where
    len = Vector.length es

lLit :: Literal -> LExpr v
lLit = pureLifted . Sized (Lit 1) . Operand . Lit

lSized
  :: (Eq v, Hashable v)
  => LExpr v
  -> LExpr v
  -> LExpr v
lSized sz e
  = letLExprs ((,) mempty <$> Vector.fromList [sz, e])
  $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B 0)
  $ Operand $ pure $ B 1

lSizedOperand
  :: (Eq v, Hashable v)
  => LExpr v
  -> Operand v
  -> LExpr v
lSizedOperand sz = lSizedInnerExpr sz . Operand

lSizedInnerExpr
  :: (Eq v, Hashable v)
  => LExpr v
  -> InnerExpr v
  -> LExpr v
lSizedInnerExpr sz e
  = letLExpr mempty sz
  $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B ()) $ F <$> e

callLExpr
  :: (Eq v, Hashable v)
  => LExpr v
  -> LExpr v
  -> Vector (LExpr v)
  -> LExpr v
callLExpr lsz le les
  = letLExprs ((,) mempty <$> Vector.cons lsz (Vector.cons le les))
  $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B 0)
  $ Call (pure $ B 1) (pure . B <$> Vector.enumFromN 2 len)
    where
      len = Vector.length les

-------------------------------------------------------------------------------
-- Bodies
liftBody
  :: (Eq v, Hashable v)
  => Body v
  -> LExpr v
liftBody (Constant e) = pureLifted e
liftBody (Function vs s)
  = Lifted (pure (mempty, f))
  $ Simple.Scope $ Sized (Lit 1)
  $ Call (pure $ B 0) $ pure . pure <$> fvs
  where
    f = Function (fmap mempty fvs <> vs)
      $ Simple.toScope
      $ unvar (B . (+ Tele fvsLen)) (unvar F $ fromJust err . ix)
     <$> Simple.fromScope (F <$> s)
    ix = Tele . fromJust err . (`Vector.elemIndex` fvs)
    err = error "liftFunction"
    fvs = Vector.fromList $ HashSet.toList $ toHashSet s
    fvsLen = Vector.length fvs

liftLBody
  :: (Eq v, Hashable v)
  => LBody v
  -> LExpr v
liftLBody lbody = bindLifted' lbody liftBody

lamLBody :: Vector NameHint -> Simple.Scope Tele LExpr v -> LBody v
lamLBody hs (Simple.Scope (Lifted bs (Simple.Scope s)))
  = Lifted bs
  $ Simple.Scope
  $ Function hs
  $ Simple.Scope
  $ commuteVars <$> s

-------------------------------------------------------------------------------
-- Instances
class BindOperand f where
  bindOperand :: (v -> Operand v') -> f v -> f v'

instance BindOperand Operand where
  bindOperand f o = o >>= f

instance BindOperand InnerExpr where
  bindOperand f expr = case expr of
    Operand o -> Operand $ bindOperand f o
    Con qc os -> Con qc $ bimap (bindOperand f) (bindOperand f) <$> os
    Call o os -> Call (bindOperand f o) (bindOperand f <$> os)

instance BindOperand Expr where
  bindOperand f expr = case expr of
    Sized o i -> Sized (bindOperand f o) (bindOperand f i)
    Let h e s -> Let h (bindOperand f e) (bindOperand f s)
    Case (x, sz) brs -> Case (bindOperand f x, bindOperand f sz) $ bindOperand f brs

instance BindOperand Body where
  bindOperand f body = case body of
    Constant e -> Constant $ bindOperand f e
    Function hs s -> Function hs $ bindOperand f s

instance BindOperand e => BindOperand (SimpleBranches c e) where
  bindOperand f (SimpleConBranches cbrs) = SimpleConBranches [(qc, bindOperand f tele, bindOperand f s) | (qc, tele, s) <- cbrs]
  bindOperand f (SimpleLitBranches lbrs def) = SimpleLitBranches (second (bindOperand f) <$> lbrs) (bindOperand f def)

instance BindOperand e => BindOperand (SimpleTelescope e) where
  bindOperand f (SimpleTelescope xs) = SimpleTelescope $ second (bindOperand f) <$> xs

instance BindOperand e => BindOperand (Simple.Scope b e) where
  bindOperand f (Simple.Scope s)
    = Simple.Scope
    $ bindOperand (unvar (pure . B) (fmap F . f)) s

instance Monad Operand where
  return = Local
  Local v >>= f = f v
  Global g >>= _ = Global g
  Lit l >>= _ = Lit l

instance Applicative Operand where
  pure = Local
  (<*>) = ap

instance Bound Lifted where
  Lifted ds d >>>= f = Lifted ds (d >>>= f)

instance Eq1 Expr
instance Ord1 Expr
instance Show1 Expr

instance (Eq v, IsString v, Pretty v, Pretty (e v), Functor e)
      => Pretty (Lifted e v) where
  prettyM (Lifted ds (Simple.Scope s)) = withNameHints (fst <$> ds) $ \ns ->
    let toName = fromText . (ns Vector.!) . unTele
        addWheres x | Vector.null ds = x
        addWheres x = x <$$> indent 2 (prettyM "where" <$$>
          indent 2 (vcat $ Vector.toList $ (\(n, (_, e)) -> prettyM n <+> prettyM "=" <+> prettyM (toName <$> e)) <$> Vector.zip ns ds))
     in addWheres $ prettyM (unvar toName id <$> s)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Body v) where
  prettyM body = case body of
    Constant e -> prettyM e
    Function hs s -> withNameHints hs $ \ns ->
      prettyM "\\" <> hsep (map prettyM $ Vector.toList ns) <> prettyM "." <+>
        associate absPrec (prettyM $ instantiateVar (fromText . (ns Vector.!) . unTele) s)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Operand v) where
  prettyM (Local v) = prettyM v
  prettyM (Global g) = prettyM g
  prettyM (Lit l) = prettyM l

instance (Eq v, IsString v, Pretty v)
      => Pretty (InnerExpr v) where
  prettyM expr = case expr of
    Operand o -> prettyM o
    Con c vs -> prettyApps
      (prettyM c)
      ((\(e, t) -> parens `above` annoPrec $ prettyM e <+> prettyM ":" <+> prettyM t) <$> vs)
    Call v vs -> prettyApps (prettyM v) (prettyM <$> vs)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Let h e s -> parens `above` letPrec $
      withNameHint h $ \n ->
        prettyM "let" <+> prettyM n <+> prettyM "=" <+> inviolable (prettyM e) <+> prettyM "in" <$$>
          indent 2 (inviolable $ prettyM $ instantiate1Var (fromText n) s)
    Case (v, sz) brs -> parens `above` casePrec $
      prettyM "case" <+> inviolable (prettyM v) <+>
      prettyM ":" <+> inviolable (prettyM sz) <+>
      prettyM "of" <$$> indent 2 (prettyM brs)
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> prettyM ":" <+> prettyM sz
