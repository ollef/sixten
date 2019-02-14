{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module TypeRep where

import Protolude hiding (TypeRep)

import Backend.Target
import Pretty

newtype TypeRep = TypeRep
  { size :: Integer
  } deriving (Eq, Ord, Show, Hashable)

product :: TypeRep -> TypeRep -> TypeRep
product (TypeRep aSize) (TypeRep bSize) = TypeRep $ aSize + bSize

sum :: TypeRep -> TypeRep -> TypeRep
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
