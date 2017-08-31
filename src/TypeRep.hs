{-# LANGUAGE PatternSynonyms, OverloadedStrings #-}
module TypeRep where

import Data.Bits

import Backend.Target
import Pretty

data TypeRep = TypeRep
  { size :: Int
  , alignment :: Int -- log_2
  } deriving (Eq, Ord, Show)

toInt :: Target -> TypeRep -> Int
toInt t (TypeRep sz al) = shiftL sz (alignBits t) .|. al

-- Note: Not associative
product :: TypeRep -> TypeRep -> TypeRep
product a Unit = a
product Unit b = b
product (TypeRep aSize aAlign) (TypeRep bSize bAlign)
  = TypeRep
    (bStart + bSize)
    (max aAlign bAlign)
  where
    bAlignMask = shiftL 1 bAlign - 1
    bStart = (aSize + bAlignMask) .&. complement bAlignMask

sum :: TypeRep -> TypeRep -> TypeRep
sum a Unit = a
sum Unit b = b
sum (TypeRep aSize aAlign) (TypeRep bSize bAlign)
  = TypeRep
    (max aSize bSize)
    (max aAlign bAlign)

pattern Unit :: TypeRep
pattern Unit = TypeRep 0 0

byte :: TypeRep
byte = TypeRep 1 0

ptr :: Target -> TypeRep
ptr t = TypeRep (ptrBytes t) (log2PtrAlign t)

int :: Target -> TypeRep
int t = TypeRep (intBytes t) (log2PtrAlign t)

typeRep :: Target -> TypeRep
typeRep = int

piRep :: Target -> TypeRep
piRep = ptr

instance Pretty TypeRep where
  prettyM (TypeRep sz al) = prettyApps "TypeRep" [prettyM sz, prettyM al]
