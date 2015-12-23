module Syntax.Name where
import Data.Text(Text)

type Name    = Text
type Constr  = Text

data QConstr = QConstr !Name !Constr
  deriving (Eq, Ord, Show)

qualify :: Name -> Either Constr QConstr -> QConstr
qualify n (Right qc@(QConstr n' _)) | n == n' = qc
qualify n (Left c) = QConstr n c
qualify n e = error $ "qualify " ++ show (n, e)

