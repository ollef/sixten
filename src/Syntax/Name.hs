{-# LANGUAGE DeriveGeneric #-}
module Syntax.Name where
import GHC.Generics(Generic)
import Data.Text(Text)
import Data.Hashable

type Name    = Text
type Constr  = Text

data QConstr = QConstr !Name !Constr
  deriving (Eq, Generic, Ord, Show)

instance Hashable QConstr

-- TODO remove?
qualify :: Name -> Either Constr QConstr -> QConstr
qualify n (Right qc@(QConstr n' _)) | n == n' = qc
qualify n (Left c) = QConstr n c
qualify n e = error $ "qualify " ++ show (n, e)

