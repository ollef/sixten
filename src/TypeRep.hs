{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module TypeRep where

import Backend.Target
import Pretty

newtype TypeRep = TypeRep
  { size :: Integer
  } deriving (Eq, Ord, Show)

product :: TypeRep -> TypeRep -> TypeRep
product a UnitRep = a
product UnitRep b = b
product (TypeRep aSize) (TypeRep bSize) = TypeRep $ aSize + bSize

sum :: TypeRep -> TypeRep -> TypeRep
sum a UnitRep = a
sum UnitRep b = b
sum (TypeRep aSize) (TypeRep bSize) = TypeRep $ max aSize bSize

pattern UnitRep :: TypeRep
pattern UnitRep = TypeRep 0

pattern ByteRep :: TypeRep
pattern ByteRep = TypeRep 1

ptrRep :: Target -> TypeRep
ptrRep t = TypeRep $ fromIntegral $ ptrBytes t

intRep :: Target -> TypeRep
intRep t = TypeRep $ fromIntegral $ intBytes t

typeRep :: Target -> TypeRep
typeRep = intRep

piRep :: Target -> TypeRep
piRep = ptrRep

instance Pretty TypeRep where
  prettyM (TypeRep sz) = prettyApp "TypeRep" $ prettyM sz
