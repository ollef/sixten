{-# LANGUAGE TypeSynonymInstances #-}
module Pretty
  (module Text.PrettyPrint.ANSI.Leijen
  , Pretty, pretty, prettyPrec
  , parensIf, bracesIf
  ) where

import Bound
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>), Pretty, pretty, prettyList)

class Pretty a where
  pretty     :: a -> Doc
  pretty = prettyPrec (-1)

  prettyPrec :: Int -> a -> Doc
  prettyPrec _ = pretty

parensIf :: Bool -> Doc -> Doc
parensIf b = if b then parens else id

bracesIf :: Bool -> Doc -> Doc
bracesIf b = if b then braces else id

instance Pretty Bool    where pretty = text . show
instance Pretty Char    where pretty = text . show
instance Pretty Int     where pretty = text . show
instance Pretty ()      where pretty = text . show
instance Pretty Integer where pretty = text . show
instance Pretty Float   where pretty = text . show
instance Pretty Double  where pretty = text . show
instance Pretty Doc     where pretty = id

instance (Pretty b, Pretty a) => Pretty (Var b a) where
  prettyPrec d (B b) = prettyPrec d b
  prettyPrec d (F a) = prettyPrec d a

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyPrec _ (a, b) = tupled [pretty a, pretty b]
