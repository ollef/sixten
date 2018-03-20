{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, OverloadedStrings #-}
module Pretty
  ( AnsiStyle, bold, italicized, underlined, red, dullGreen, dullBlue
  , Doc
  , Pretty, PrettyM, PrettyNamed
  , runPrettyM
  , (<+>), (<$$>)
  , align, indent, hcat, vcat, hsep
  , absPrec, annoPrec, appPrec, arrPrec, casePrec, letPrec
  , above
  , associate
  , inviolable
  , angles, brackets, braces, parens
  , pretty
  , prettyApp, prettyApps, prettyTightApp
  , prettyList
  , prettyM
  , prettyNamed
  , showWide
  , prettyHumanList
  , withName, withHint
  , withNameHint, withNameHints
  ) where

import Bound
import Control.Monad.Reader
import qualified Data.Foldable as Foldable
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Proxy
import Data.String
import Data.Text(Text)
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as PP
import Data.Text.Prettyprint.Doc.Render.Terminal(AnsiStyle)
import qualified Data.Text.Prettyprint.Doc.Render.Terminal as PP
import qualified Data.Text.Prettyprint.Doc.Render.Text as RenderText
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.Void

import Syntax.Name
import Syntax.NameHint

infixr 6 <+>

-------------------------------------------------------------------------------
-- * The pretty type and class
-------------------------------------------------------------------------------
newtype PrettyM a = PrettyM (PrettyEnv -> a)
  deriving (Functor, Applicative, Monad, MonadReader PrettyEnv, Monoid)

type Doc = PP.Doc AnsiStyle

data PrettyEnv = PrettyEnv
  { precedence :: !Int -- ^ The precedence of the surrounding expression
  , boundNames :: !(HashSet Name)
  , freeNames :: [Name]
  }

class Pretty a where
  pretty :: a -> Doc
  pretty = runPrettyM . prettyM
  prettyM :: a -> PrettyM Doc
  prettyM = return . pretty
  prettyList :: [a] -> PrettyM Doc
  prettyList xs = PP.list <$> mapM (inviolable . prettyM) xs

class PrettyNamed a where
  prettyNamed :: PrettyM Doc -> a -> PrettyM Doc

runPrettyM :: PrettyM a -> a
runPrettyM (PrettyM p) = p PrettyEnv
  { precedence = -1
  , boundNames = mempty
  , freeNames = do
    n <- [(0 :: Int)..]
    c <- ['a'..'z']
    return $ fromString $ c : if n == 0 then "" else show n
  }

-------------------------------------------------------------------------------
-- * Doc helpers
-------------------------------------------------------------------------------
(<+>), (<$$>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
a <+> b = (PP.<+>) <$> a <*> b
a <$$> b = (\x y -> x <> PP.line <> y) <$> a <*> b

vcat :: Foldable f => f (PrettyM Doc) -> PrettyM Doc
vcat xs = PP.vcat <$> sequence (Foldable.toList xs)

hcat :: Foldable f => f (PrettyM Doc) -> PrettyM Doc
hcat xs = PP.hcat <$> sequence (Foldable.toList xs)

hsep :: Foldable f => f (PrettyM Doc) -> PrettyM Doc
hsep xs = PP.hsep <$> sequence (Foldable.toList xs)

align :: PrettyM Doc -> PrettyM Doc
align = fmap PP.align

indent :: Int -> PrettyM Doc -> PrettyM Doc
indent n = fmap $ PP.indent n

showWide :: Doc -> Text
showWide d = RenderText.renderStrict $ PP.layoutSmart opts d
  where
    opts = PP.defaultLayoutOptions
      { PP.layoutPageWidth = PP.Unbounded }

prettyHumanListM :: Pretty a => Text -> [a] -> PrettyM Doc
prettyHumanListM conjunct [x, y] = prettyM x <+> prettyM conjunct <+> prettyM y
prettyHumanListM conjunct xs = go xs
  where
    go [] = "(empty)"
    go [x] = prettyM x
    go [x, y] = prettyM x <> "," <+> prettyM conjunct <+> prettyM y
    go (x:xs') = prettyM x <> "," <+> go xs'

prettyHumanList :: Pretty a => Text -> [a] -> Doc
prettyHumanList conjunct = runPrettyM . prettyHumanListM conjunct

bold, italicized, underlined, red, dullBlue, dullGreen :: Doc -> Doc
bold = PP.annotate PP.bold
italicized = PP.annotate PP.bold
underlined = PP.annotate PP.underlined
red = PP.annotate $ PP.color PP.Red
dullBlue = PP.annotate $ PP.colorDull PP.Blue
dullGreen = PP.annotate $ PP.colorDull PP.Green

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
withName :: (Name -> PrettyM a) -> PrettyM a
withName k = do
  name:fnames <- asks freeNames
  local (\env -> env {freeNames = fnames}) $ withHint name k

withHint :: Name -> (Name -> PrettyM a) -> PrettyM a
withHint name k = do
  bnames <- asks boundNames
  let candidates = name : [name <> fromString (show n) | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  local (\env -> env {boundNames = bnames'}) $ k actualName

withNameHint :: NameHint -> (Name -> PrettyM a) -> PrettyM a
withNameHint (NameHint name) = withHint name
withNameHint NoHint = withName

withNameHints :: Vector NameHint -> (Vector Name -> PrettyM a) -> PrettyM a
withNameHints v k = go (Vector.toList v) $ k . Vector.fromList
  where
    go :: [NameHint] -> ([Name] -> PrettyM a) -> PrettyM a
    go [] k' = k' []
    go (hint:hints) k' =
      withNameHint hint (\name -> go hints (\names -> k' (name : names)))

-------------------------------------------------------------------------------
-- * Working with precedence
-------------------------------------------------------------------------------
absPrec, annoPrec, appPrec, tightAppPrec, arrPrec, casePrec, letPrec :: Int
absPrec  = 1
annoPrec = 0
appPrec  = 11
tightAppPrec = 12
arrPrec  = 1
casePrec = 1
letPrec  = 1

above :: (PrettyM a -> PrettyM a) -> Int -> PrettyM a -> PrettyM a
above f p' m = do
  p <- asks precedence
  (if p > p' then f else id) $ associate (p' + 1) m

prettyApp :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
prettyApp p q = parens `above` appPrec $ associate appPrec p <+> q

prettyApps :: Foldable t => PrettyM Doc -> t (PrettyM Doc) -> PrettyM Doc
prettyApps = foldl prettyApp

prettyTightApp :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
prettyTightApp p q = parens `above` tightAppPrec $ associate tightAppPrec p <> q

associate :: Int -> PrettyM a -> PrettyM a
associate p = local $ \s -> s {precedence = p}

inviolable :: PrettyM a -> PrettyM a
inviolable = local $ \s -> s {precedence = -1}

angles, braces, brackets, parens :: PrettyM Doc -> PrettyM Doc
angles = fmap PP.angles . inviolable
braces = fmap PP.braces . inviolable
brackets = fmap PP.brackets . inviolable
parens = fmap PP.parens . inviolable

-------------------------------------------------------------------------------
-- * Instances
-------------------------------------------------------------------------------
instance a ~ Doc => IsString (PrettyM a) where
  fromString = PrettyM . const . fromString

instance Pretty Bool where pretty = fromString . show
instance Pretty Char where
  pretty = fromString . show
  prettyList = pure . fromString
instance Pretty Int where pretty = fromString . show
instance Pretty () where pretty = fromString . show
instance Pretty Integer where pretty = fromString . show
instance Pretty Float  where pretty = fromString . show
instance Pretty Double where pretty = fromString . show
instance a ~ AnsiStyle => Pretty (PP.Doc a) where pretty = id
instance Pretty Text where pretty = fromString . Text.unpack
instance Pretty PreName where pretty (PreName n) = pretty n
instance Pretty Name where pretty (Name n) = pretty n
instance Pretty Constr where pretty (Constr c) = pretty c
instance Pretty Void where pretty = absurd

instance Pretty a => Pretty [a] where prettyM = prettyList
instance Pretty a => Pretty (Vector a) where prettyM = prettyM . Vector.toList

instance Pretty a => Pretty (Maybe a) where
  prettyM Nothing = "Nothing"
  prettyM (Just b) = prettyApp "Just" (prettyM b)

instance (Pretty b, Pretty a) => Pretty (Var b a) where
  prettyM (B b) = prettyApp "B" (prettyM b)
  prettyM (F a) = prettyApp "F" (prettyM a)

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  prettyM (Left a) = prettyApp "Left" (prettyM a)
  prettyM (Right b) = prettyApp "Right" (prettyM b)

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyM (a, b) = inviolable $ f
    <$> prettyM a
    <*> prettyM b
    where
      f x y = PP.tupled [x, y]

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  prettyM (a, b, c) = inviolable $ f
    <$> prettyM a
    <*> prettyM b
    <*> prettyM c
    where
      f x y z = PP.tupled [x, y, z]

instance Pretty a => Pretty (HashSet a) where
  prettyM s
    = PP.encloseSep PP.lbrace PP.rbrace PP.comma <$> mapM (inviolable . prettyM) (HashSet.toList s)

instance Pretty (Proxy a) where
  prettyM Proxy = "Proxy"
