{-# LANGUAGE FlexibleContexts, TypeSynonymInstances #-}
module Pretty
  (module Text.PrettyPrint.ANSI.Leijen
  , Pretty, pretty, prettyPrec
  , above, withName, withSuggestedName, withHint, associate, inviolable
  , bracesWhen, parensWhen, prettyApp
  , appPrec, absPrec, arrPrec, annoPrec, casePrec, letPrec
  ) where

import Bound
import Control.Applicative
import Control.Monad.Reader
import Data.Monoid
import Data.Set(Set)
import qualified Data.Set as S
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>), Pretty, empty, pretty, prettyList)

import Util

appPrec, absPrec, arrPrec, annoPrec, casePrec, letPrec :: Int
appPrec    = 11
absPrec    =  1
arrPrec    =  1
annoPrec   =  0
casePrec   =  1
letPrec    =  1

names :: [Name]
names = do
  n <- [(0 :: Int)..]
  c <- ['a'..'z']
  return $ c : if n == 0 then "" else show n

data PrettyState = PrettyState
  { precedence :: !Int
  , boundNames :: !(Set Name)
  , freeNames  :: ![Name] -- ^ Invariant: Does not contain any name in bound names
  }

type PrettyM a = PrettyState -> a

class Pretty a where
  pretty     :: a -> Doc
  pretty a = prettyPrec a $ PrettyState (-1) mempty names

  prettyPrec :: a -> PrettyM Doc
  prettyPrec = return . pretty

  prettyList :: [a] -> PrettyM Doc
  prettyList xs = list <$> mapM (inviolable . prettyPrec) xs

above :: (a -> a) -> Int -> PrettyM a -> PrettyM a
above f p' m = do
  p <- asks precedence
  let g = if p > p' then f else id
  local (\s -> s {precedence = p' + 1}) $ g <$> m

withName :: (Name -> PrettyM a) -> PrettyM a
withName f = do
  x:xs <- asks freeNames
  local (\s -> s {boundNames = S.insert x $ boundNames s, freeNames = xs}) $ f x

withSuggestedName :: Name -> (Name -> PrettyM a) -> PrettyM a
withSuggestedName n f = do
  bs <- asks boundNames
  if n `S.member` bs then
    withSuggestedName (n ++ "'") f
  else
    local (\s -> s { boundNames = S.insert n bs
                   , freeNames = filter (/= n) $ freeNames s })
          (f n)

withHint :: Hint (Maybe Name) -> (Name -> PrettyM a) -> PrettyM a
withHint (Hint Nothing)  = withName
withHint (Hint (Just n)) = withSuggestedName n

associate :: PrettyM a -> PrettyM a
associate = local $ \s -> s {precedence = precedence s - 1}

inviolable :: PrettyM a -> PrettyM a
inviolable = local $ \s -> s {precedence = -1}

bracesWhen ::  Bool -> PrettyM Doc -> PrettyM Doc
bracesWhen b m = if b then braces <$> inviolable m else m

parensWhen ::  Bool -> PrettyM Doc -> PrettyM Doc
parensWhen b m = if b then parens <$> inviolable m else m

prettyApp :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
prettyApp p q = parens `above` appPrec $ (<+>) <$> associate p <*> q

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

instance Pretty a => Pretty [a] where prettyPrec = prettyList

instance (Pretty b, Pretty a) => Pretty (Var b a) where
  prettyPrec (B b) = prettyApp (pure $ text "B") (prettyPrec b)
  prettyPrec (F a) = prettyApp (pure $ text "F") (prettyPrec a)

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyPrec (a, b) = inviolable $ f <$> prettyPrec a
                                     <*> prettyPrec b
    where f x y = tupled [x, y]
instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  prettyPrec (a, b, c) = inviolable $ f <$> prettyPrec a
                                        <*> prettyPrec b
                                        <*> prettyPrec c
    where f x y z = tupled [x, y, z]

instance Pretty a => Pretty (Hint a) where prettyPrec (Hint x) = prettyPrec x
