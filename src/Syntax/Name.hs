module Syntax.Name where
import Data.Text(Text)

type Name    = Text
type Constr  = Text

data QConstr = QConstr !Name !Constr
  deriving (Eq, Ord, Show)
