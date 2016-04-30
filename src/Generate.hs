{-# LANGUAGE DeriveFunctor, OverloadedStrings, RecursiveDo #-}
module Generate where

import Bound
import qualified Data.Foldable as Foldable
import Data.List
import Data.Monoid
import Data.Text(Text)
import qualified Data.Traversable as Traversable
import qualified Data.Vector as Vector

import Syntax.Branches
import Syntax.Lifted
import Syntax.Name
import Syntax.Telescope
import TCM
import Util

type B = Text

int, ptr, align, void :: B
int = "i64"
ptr = int <> "*"
align = "8"
void = "void"

(<+>) :: B -> B -> B
x <+> y = x <> " " <> y
infixr 6 <+>

indent :: [B] -> [B]
indent = map ("  " <>)

type OperandB = Operand B
type ExprB = Expr B
type BodyB e = Body e B
type BranchesB e = Branches QConstr e B

adds :: Foldable f => f OperandB -> TCM s ([B], [B], B)
adds = Foldable.foldlM go ([], [], "0")
  where
    go (xs, ys, v) o = do
      i <- fresh
      let name = "%" <> shower i
      return ( xs <> pure (name =: "add" <+> int <+> v <> "," <+> generateOperand o)
             , ys <> pure v
             , name
             )

memcpy :: B -> B -> B -> B
memcpy dst src sz
  = "call void @llvm.memcpy.p0i8.p0i8.i64(i8* bitcast ("
  <> ptr <+> dst <+> "to i8*)," <+> "i8* bitcast ("
  <> ptr <+> src <+> "to i8*),"
  <+> int <+> sz <> ", i64" <+> align <> ", i1 false)"

getElementPtr :: B -> B -> B
getElementPtr x i = "getelementptr" <+> int <> "," <+> ptr <+> x <> "," <+> int <+> i

alloca :: B -> B
alloca sz = "alloca" <+> int <> "," <+> int <+> sz <> ", align" <+> align

br :: B -> B
br l = "br label" <+> l

(=:) :: B -> B -> B
x =: y = x <+> "=" <+> y
infixr 6 =:

switch :: B -> B -> [(Int, B)] -> B
switch e def brs
  = "switch" <+> int <+> e <> ", label" <+> def
  <+> "[" <> Foldable.fold (intersperse ", " $ (\(i, l) -> int <+> shower i <> ", label" <+> l) <$> brs)
  <> "]"

phi :: [(B, B)] -> B
phi xs
  = "phi" <+> ptr <+> Foldable.fold (intersperse ", " $ (\(v, l) -> "[" <> v <> "," <+> l <> "]") <$> xs)

generateOperand :: OperandB -> B
generateOperand op = case op of
  Local l -> l
  Global g -> "@" <> g -- TODO constants?
  Lit l -> shower l

generateExpr :: ExprB -> TCM s ([B], B)
generateExpr expr = case expr of
  Operand o -> return (mempty, generateOperand o)
  Con qc os -> do
    qcIndex <- constrIndex qc
    let os' = Vector.cons (Lit $ fromIntegral qcIndex, Lit 1) os
    (bs, is, fullSize) <- adds $ snd <$> os'
    result <- ("%" <>) . shower <$> fresh
    copies <- Traversable.forM (zip is $ Vector.toList os') $ \(i, (o, sz)) -> do
      index <- ("%" <>) . shower <$> fresh
      return
        [ index =: getElementPtr result i
        , memcpy index (generateOperand o) (generateOperand sz)
        ]
    return
      ( bs <> pure (result =: alloca fullSize)
      <> concat copies
      , result
      )
  Let h e s -> do
    (bs, i) <- generateExpr e
    (bs', i') <- generateExpr $ instantiate1 (pure i) s
    return (bs <> bs', i')
  Call sz o os -> do
    name <- ("%" <>) . shower <$> fresh
    return
      ( pure (name =: alloca (generateOperand sz))
      <> pure ("call" <+> void <+> generateOperand o <> "(" <> Foldable.fold (intersperse ", " $ Vector.toList $ (generateOperand <$> os) <> pure name) <> ")")
      , name
      )
  Case o brs -> generateBranches (generateOperand o) brs
  Error -> return (pure "call void @exit(i32 1)", "undef")

generateBranches :: B -> BranchesB Expr -> TCM s ([B], B)
generateBranches expr branches = case branches of
  ConBranches cbrs _ -> do
    postLabel <- ("%" <>) . shower <$> fresh
    cbrs' <- Traversable.forM cbrs $ \(qc, tele, brScope) -> mdo
      qcIndex <- constrIndex qc
      let inst = instantiateTele $ pure . snd <$> args
      args <- forMTele tele $ \h _ sz -> do
        (szBs, szv) <- generateExpr $ inst sz
        return (szBs, szv)
      (addBs, is, _) <- adds $ Vector.cons (Lit 1) $ Local . snd <$> args
      let ixBs = [v =: getElementPtr expr i | (i, (_, v)) <- zip is $ Vector.toList args]
          szBss = Foldable.fold $ fst <$> args
      (branchBs, branchResult) <- generateExpr $ inst brScope
      label <- ("%" <>) . shower <$> fresh
      return (qcIndex, label, pure (label <> ":") <> (indent $ szBss <> addBs <> ixBs <> branchBs <> pure (br postLabel)), branchResult)

    e0 <- ("%" <>) . shower <$> fresh
    result <- ("%" <>) . shower <$> fresh
    let caseBs =
          [ e0 =: getElementPtr expr "0"
          , switch e0 "%patternmatchfailed" [(qcIndex, l) | (qcIndex, l, _, _) <- cbrs']
          ]
        branchBs = concat [bs | (_, _, bs, _) <- cbrs']
        postBs =
          [ postLabel <> ":"
          , result =: phi [(res, l) | (_, l, _, res) <- cbrs']
          ]

    return (caseBs <> branchBs <> postBs, result)
  LitBranches _ _ -> undefined

generateBody :: BodyB Expr -> TCM s B
generateBody body = case body of
  Constant _ -> error "generateBody Constant"
  Function hs e -> do
    vs <- Traversable.forM hs $ \h -> ("%" <>) . shower <$> fresh
    (bs, b) <- generateExpr $ instantiate (pure . (vs Vector.!) . unTele) e
    retptr <- ("%" <>) . shower <$> fresh
    retvar <- ("%" <>) . shower <$> fresh
    let header = pure $ "(" <> Foldable.fold (intersperse ", " $ (ptr <+>) <$> Vector.toList vs) <> "," <+> ptr <> "*" <+> retptr <> ")"
        footer =
          [ retvar =: getElementPtr retptr "0"
          , memcpy retvar b "TODO" -- bsize
          ]
    return $ mconcat $ intersperse "\n" $ header <> bs <> footer

