module Syntax.Pretty
  ( module Text.PrettyPrint.ANSI.Leijen
  , Pretty
  , (<+>), (<$$>)
  , indent, hcat, vcat, hsep
  , iff
  , above
  , absPrec, annoPrec, appPrec, arrPrec, casePrec, dotPrec, letPrec
  , associate
  , inviolable
  , angles, brackets, braces, parens
  , pretty
  , prettyApp
  , prettyList
  , prettyM
  , tilde
  , showWide
  , withName, withHint
  , withNameHint, withNameHints
  ) where
import Bound
import Control.Monad.Reader
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid
import Data.Text(Text)
import qualified Data.Text as Text
import Data.Vector(Vector)
import qualified Data.Vector as Vector
import Data.String
import Text.PrettyPrint.ANSI.Leijen
  ( Doc
  , list
  , putDoc
  , text
  , tupled
  )
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen

import Syntax.Hint
import Util

-------------------------------------------------------------------------------
-- * The pretty type and class
-------------------------------------------------------------------------------
type PrettyM a = PrettyEnv -> a

data PrettyEnv = PrettyEnv
  { precedence :: !Int -- ^ The precedence of the surrounding expression
  , boundNames :: !(HashSet Name)
  , freeNames  :: [Name]
  }

class Pretty a where
  pretty  :: a -> Doc
  pretty x = prettyM x PrettyEnv
    { precedence = -1
    , boundNames = mempty
    , freeNames  = do
      n <- [(0 :: Int)..]
      c <- ['a'..'z']
      return $ fromString $ c : if n == 0 then "" else show n
    }
  prettyM :: a -> PrettyM Doc
  prettyM = return . pretty
  prettyList :: [a] -> PrettyM Doc
  prettyList xs = list <$> mapM (inviolable . prettyM) xs

-------------------------------------------------------------------------------
-- * Doc helpers
-------------------------------------------------------------------------------
(<+>), (<$$>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
a <+> b = (Leijen.<+>) <$> a <*> b
a <$$> b = (Leijen.<$$>) <$> a <*> b

vcat :: [PrettyM Doc] -> PrettyM Doc
vcat xs = Leijen.vcat <$> sequence xs

hcat :: [PrettyM Doc] -> PrettyM Doc
hcat xs = Leijen.vcat <$> sequence xs

hsep :: [PrettyM Doc] -> PrettyM Doc
hsep xs = Leijen.hsep <$> sequence xs

indent :: Int -> PrettyM Doc -> PrettyM Doc
indent n = fmap $ Leijen.indent n

tilde :: Doc
tilde = Leijen.text "~"

showWide :: Doc -> String
showWide d = Leijen.displayS (Leijen.renderPretty 1.0 200 d) ""

-------------------------------------------------------------------------------
-- * Working with names
-------------------------------------------------------------------------------
withName :: (Name -> PrettyM a) -> PrettyM a
withName k = do
  name:fnames <- asks freeNames
  local (\env -> env {freeNames = fnames}) $ withHint (Hint name) k

withHint :: Hint Name -> (Name -> PrettyM a) -> PrettyM a
withHint (Hint name) k = do
  bnames <- asks boundNames
  let candidates = name : [name <> fromString (show n) | n <- [(1 :: Int)..]]
      actualName = head $ filter (not . (`HashSet.member` bnames)) candidates
      bnames' = HashSet.insert actualName bnames
  local (\env -> env {boundNames = bnames'}) $ k actualName

withNameHint :: NameHint -> (Name -> PrettyM a) -> PrettyM a
withNameHint (Hint (Just name)) = withHint (Hint name)
withNameHint (Hint Nothing) = withName

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
absPrec, annoPrec, appPrec, arrPrec, casePrec, dotPrec, letPrec :: Int
absPrec    =  1
annoPrec   =  0
appPrec    = 11
arrPrec    =  1
casePrec   =  1
dotPrec    = 12
letPrec    =  1

iff :: (PrettyM a -> PrettyM a) -> Bool -> PrettyM a -> PrettyM a
iff f True  m = f m
iff _ False m = m

above :: (PrettyM a -> PrettyM a) -> Int -> PrettyM a -> PrettyM a
above f p' m = do
  p <- asks precedence
  local (\env -> env {precedence = p' + 1}) $ f `iff` (p > p') $ m

prettyApp :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
prettyApp p q = parens `above` appPrec $ associate p <+> q

associate :: PrettyM a -> PrettyM a
associate = local $ \s -> s {precedence = precedence s - 1}

inviolable :: PrettyM a -> PrettyM a
inviolable = local $ \s -> s {precedence = -1}

angles, braces, brackets, parens :: PrettyM Doc -> PrettyM Doc
angles = fmap Leijen.angles . inviolable
braces = fmap Leijen.braces . inviolable
brackets = fmap Leijen.brackets . inviolable
parens = fmap Leijen.parens . inviolable

-------------------------------------------------------------------------------
-- * Instances
-------------------------------------------------------------------------------
instance Pretty Bool    where pretty = text . show
instance Pretty Char    where
  pretty = text . show
  prettyList = pure . text
instance Pretty Int     where pretty = text . show
instance Pretty ()      where pretty = text . show
instance Pretty Integer where pretty = text . show
instance Pretty Float   where pretty = text . show
instance Pretty Double  where pretty = text . show
instance Pretty Doc     where pretty = id
instance Pretty Text    where pretty = text . Text.unpack

instance Pretty a => Pretty [a] where prettyM = prettyList

instance Pretty a => Pretty (Maybe a) where
  prettyM Nothing  = pure $ text "Nothing"
  prettyM (Just b) = prettyApp (pure $ text "Just") (prettyM b)

instance (Pretty b, Pretty a) => Pretty (Var b a) where
  prettyM (B b) = prettyApp (pure $ text "B") (prettyM b)
  prettyM (F a) = prettyApp (pure $ text "F") (prettyM a)

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  prettyM (Left a)  = prettyApp (pure $ text "Left")  (prettyM a)
  prettyM (Right b) = prettyApp (pure $ text "Right") (prettyM b)

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyM (a, b) = inviolable $ f <$> prettyM a
                                  <*> prettyM b
    where f x y = tupled [x, y]

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  prettyM (a, b, c) = inviolable $ f <$> prettyM a
                                     <*> prettyM b
                                     <*> prettyM c
    where f x y z = tupled [x, y, z]
