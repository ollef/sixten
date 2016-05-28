{-# LANGUAGE DeriveFoldable, DeriveFunctor, DeriveGeneric, DeriveTraversable, FlexibleContexts, Rank2Types, ViewPatterns, OverloadedStrings #-}
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

data Lifted e v = Lifted (Vector (NameHint, Function Tele)) (Simple.Scope Tele e v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Direction = Direct | Indirect
  deriving (Eq, Ord, Show)

data Body v
  = ConstantBody (Stmt v)
  | FunctionBody (Function v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Function v = Function Direction (Vector (NameHint, Direction)) (Simple.Scope Tele Stmt v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

type LBody = Lifted Body
type LFunction = Lifted Function
type LStmt = Lifted Stmt
type LBranches = Lifted (SimpleBranches QConstr Stmt)

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

data Stmt v
  = Sized (Operand v) (Expr v)
  | Let NameHint (Stmt v) (Simple.Scope () Stmt v)
  | Case (Operand v, Operand v) (SimpleBranches QConstr Stmt v)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data Expr v
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
  -> Function Void
  -> Simple.Scope () e v
  -> Lifted e v
singleLifted h b s = Lifted (pure (h, vacuous b)) $ Simple.mapBound (\() -> Tele 0) s

-------------------------------------------------------------------------------
-- Statements
letStmt :: NameHint -> Stmt v -> Simple.Scope () Stmt v -> Stmt v
letStmt _ e (Simple.Scope (Sized _ (Operand (Local (B ()))))) = e
letStmt _ (Sized _ (Operand o)) s = instantiateOperand (\() -> o) s
letStmt h e s = Let h e s

letStmts :: Vector (NameHint, Stmt v) -> Simple.Scope Int Stmt v -> Stmt v
letStmts es s = unvar (error "Lifted.letExprs") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go :: (Int, (NameHint, Stmt v)) -> Stmt (Var Int v) -> Stmt (Var Int v)
    go (n, (h, e)) e' = letStmt h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

callStmt :: Stmt v -> Stmt v -> Vector (Stmt v) -> Stmt v
callStmt sz e es
  = letStmts ((,) mempty <$> Vector.cons sz (Vector.cons e es))
  $ Simple.Scope
  $ Sized (pure $ B 0)
  $ Call (pure $ B 1) $ pure . B <$> Vector.enumFromN 2 (Vector.length es)

conStmt :: Stmt v -> QConstr -> Vector (Stmt v, Stmt v) -> Stmt v
conStmt sz qc (Vector.unzip -> (es, szs))
  = letStmts ((,) mempty <$> Vector.cons sz (es <> szs))
  $ Simple.Scope $ Sized (pure $ B 0)
  $ Con qc $ Vector.zip (pure . B <$> Vector.enumFromN 1 len)
                        (pure . B <$> Vector.enumFromN (len + 1) len)
  where
    len = Vector.length es

caseStmt :: (Stmt v, Stmt v) -> SimpleBranches QConstr Stmt v -> Stmt v
caseStmt (e, esz) brs
  = letStmts ((,) mempty <$> Vector.fromList [e, esz])
  $ Simple.Scope $ Case (pure $ B 0, pure $ B 1) $ F <$> brs

-------------------------------------------------------------------------------
-- Lifted statements
letLStmt
  :: (Eq v, Hashable v)
  => NameHint
  -> LStmt v
  -> Simple.Scope () LStmt v
  -> LStmt v
letLStmt h lstmt (Simple.Scope lstmt')
  = bindLifted lstmt
  $ \expr -> bindLifted lstmt'
  $ \expr' -> pureLifted
  $ letStmt h (F <$> expr)
  $ Simple.Scope $ fmap (fmap F) . commuteVars <$> expr'

commuteVars :: Var a (Var b c) -> Var b (Var a c)
commuteVars = unvar (F . B) (unvar B (F . F))

letLStmts
  :: (Eq v, Hashable v)
  => Vector (NameHint, LStmt v)
  -> Simple.Scope Int LStmt v
  -> LStmt v
letLStmts es s = unvar (error "Lifted.letLStmts") id <$> foldr go (Simple.fromScope s) (Vector.indexed es)
  where
    go (n, (h, e)) e' = letLStmt h (F <$> e) $ Simple.abstract f e'
      where
        f (B n') | n == n' = Just ()
        f _ = Nothing

caseLStmt
  :: (Eq v, Hashable v)
  => (LStmt v, LStmt v)
  -> LBranches v
  -> LStmt v
caseLStmt (b, bsz) brs
  = letLStmts ((,) mempty <$> Vector.fromList [b, bsz])
  $ Simple.Scope
  $ mapLifted (Case (pure $ F $ B 0, pure $ F $ B 1) . fmap (fmap F)) brs

conLStmtBranches
  :: (Eq v, Hashable v)
  => [(QConstr, Vector (NameHint, Simple.Scope Tele LStmt v), Simple.Scope Tele LStmt v)]
  -> LBranches v
conLStmtBranches brs
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

litLStmtBranches
  :: (Eq v, Hashable v)
  => [(Literal, LStmt v)]
  -> LStmt v
  -> LBranches v
litLStmtBranches lbrs ldef
  = bindLifted ldef
  $ \def -> bindLiftedVector (Vector.fromList $ snd <$> lbrs)
  $ \brs -> pureLifted
  $ SimpleLitBranches (zip (fst <$> lbrs) $ Vector.toList $ fmap (fmap F) <$> brs) (F <$> def)

conLStmt
  :: (Eq v, Hashable v)
  => LStmt v
  -> QConstr
  -> Vector (LStmt v, LStmt v)
  -> LStmt v
conLStmt sz qc (Vector.unzip -> (es, szs))
  = letLStmts ((,) mempty <$> Vector.cons sz (es <> szs)) $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B 0)
  $ Con qc $ Vector.zip (pure . B <$> Vector.enumFromN 1 len)
                        (pure . B <$> Vector.enumFromN (len + 1) len)
  where
    len = Vector.length es

lLit :: Literal -> LStmt v
lLit = pureLifted . Sized (Lit 1) . Operand . Lit

lSized
  :: (Eq v, Hashable v)
  => LStmt v
  -> LStmt v
  -> LStmt v
lSized sz e
  = letLStmts ((,) mempty <$> Vector.fromList [sz, e])
  $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B 0)
  $ Operand $ pure $ B 1

lSizedOperand
  :: (Eq v, Hashable v)
  => LStmt v
  -> Operand v
  -> LStmt v
lSizedOperand sz = lSizedInnerExpr sz . Operand

lSizedInnerExpr
  :: (Eq v, Hashable v)
  => LStmt v
  -> Expr v
  -> LStmt v
lSizedInnerExpr sz e
  = letLStmt mempty sz
  $ Simple.Scope
  $ pureLifted
  $ Sized (pure $ B ()) $ F <$> e

callLStmt
  :: (Eq v, Hashable v)
  => LStmt v
  -> LStmt v
  -> Vector (LStmt v)
  -> LStmt v
callLStmt lsz le les
  = letLStmts ((,) mempty <$> Vector.cons lsz (Vector.cons le les))
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
  -> LStmt v
liftBody (ConstantBody e) = pureLifted e
liftBody (FunctionBody (Function d vs s))
  = Lifted (pure (mempty, f))
  $ Simple.Scope $ Sized (Lit 1)
  $ Call (pure $ B 0) $ pure . pure <$> fvs
  where
    f = Function d (fmap (const (mempty, Indirect)) fvs <> vs)
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
  -> LStmt v
liftLBody lbody = bindLifted' lbody liftBody

lamLBody
  :: Direction
  -> Vector (NameHint, Direction)
  -> Simple.Scope Tele LStmt v
  -> LBody v
lamLBody d hs (Simple.Scope (Lifted bs (Simple.Scope s)))
  = Lifted bs
  $ Simple.Scope
  $ FunctionBody
  $ Function d hs
  $ Simple.Scope
  $ commuteVars <$> s

-------------------------------------------------------------------------------
-- Instances
class BindOperand f where
  bindOperand :: (v -> Operand v') -> f v -> f v'

instance BindOperand Operand where
  bindOperand f o = o >>= f

instance BindOperand Expr where
  bindOperand f expr = case expr of
    Operand o -> Operand $ bindOperand f o
    Con qc os -> Con qc $ bimap (bindOperand f) (bindOperand f) <$> os
    Call o os -> Call (bindOperand f o) (bindOperand f <$> os)

instance BindOperand Stmt where
  bindOperand f expr = case expr of
    Sized o i -> Sized (bindOperand f o) (bindOperand f i)
    Let h e s -> Let h (bindOperand f e) (bindOperand f s)
    Case (x, sz) brs -> Case (bindOperand f x, bindOperand f sz) $ bindOperand f brs

instance BindOperand Body where
  bindOperand f body = case body of
    ConstantBody e -> ConstantBody $ bindOperand f e
    FunctionBody fb -> FunctionBody $ bindOperand f fb

instance BindOperand Function where
  bindOperand f (Function d vs s) = Function d vs $ bindOperand f s

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

instance Eq1 Stmt
instance Ord1 Stmt
instance Show1 Stmt

instance (Eq v, IsString v, Pretty v, Pretty (e v), Functor e)
      => Pretty (Lifted e v) where
  prettyM (Lifted ds (Simple.Scope s)) = withNameHints (fst <$> ds) $ \ns ->
    let toName = fromText . (ns Vector.!) . unTele
        addWheres x | Vector.null ds = x
        addWheres x = x <$$> indent 2 ("where" <$$>
          indent 2 (vcat $ Vector.toList $ (\(n, (_, e)) -> prettyM n <+> "=" <+> prettyM (toName <$> e)) <$> Vector.zip ns ds))
     in addWheres $ prettyM (unvar toName id <$> s)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Body v) where
  prettyM body = case body of
    ConstantBody e -> prettyM e
    FunctionBody f -> prettyM f

instance (Eq v, IsString v, Pretty v)
      => Pretty (Function v) where
  prettyM (Function _ hs s) = withNameHints (fst <$> hs) $ \ns ->
    "\\" <> hsep (map prettyM $ Vector.toList ns) <> "." <+>
      associate absPrec (prettyM $ instantiateVar (fromText . (ns Vector.!) . unTele) s)


instance (Eq v, IsString v, Pretty v)
      => Pretty (Operand v) where
  prettyM (Local v) = prettyM v
  prettyM (Global g) = prettyM g
  prettyM (Lit l) = prettyM l

instance (Eq v, IsString v, Pretty v)
      => Pretty (Expr v) where
  prettyM expr = case expr of
    Operand o -> prettyM o
    Con c vs -> prettyApps
      (prettyM c)
      ((\(e, t) -> parens `above` annoPrec $ prettyM e <+> ":" <+> prettyM t) <$> vs)
    Call v vs -> prettyApps (prettyM v) (prettyM <$> vs)

instance (Eq v, IsString v, Pretty v)
      => Pretty (Stmt v) where
  prettyM expr = case expr of
    Let h e s -> parens `above` letPrec $
      withNameHint h $ \n ->
        "let" <+> prettyM n <+> "=" <+> inviolable (prettyM e) <+> "in" <$$>
          indent 2 (inviolable $ prettyM $ instantiate1Var (fromText n) s)
    Case (v, sz) brs -> parens `above` casePrec $
      "case" <+> inviolable (prettyM v) <+>
      ":" <+> inviolable (prettyM sz) <+>
      "of" <$$> indent 2 (prettyM brs)
    Sized sz e -> parens `above` annoPrec $
      prettyM e <+> ":" <+> prettyM sz
