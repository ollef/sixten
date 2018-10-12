{-# LANGUAGE OverloadedStrings #-}
module Backend.Target where

import Prelude(String)
import Protolude

import qualified Data.List as List

import Error
import Pretty

-- | The number of bits in a byte.
byteBits :: Word32
byteBits = 8

data Target = Target
  { architecture :: String
  , ptrBytes :: Word32 -- ^ The number of bytes in a pointer.
  , ptrAlign :: Word32 -- ^ The alignment of a pointer.
  } deriving (Eq, Ord, Show)

x86 :: Target
x86 = Target
  { architecture = "x86"
  , ptrBytes = 4
  , ptrAlign = 4
  }

x86_64 :: Target
x86_64 = Target
  { architecture = "x86-64"
  , ptrBytes = 8
  , ptrAlign = 8
  }

-- | The number of bits in a pointer.
ptrBits :: Target -> Word32
ptrBits t = byteBits * ptrBytes t

intBytes, intBits :: Target -> Word32
intBytes = ptrBytes
intBits = ptrBits

targets :: [Target]
targets = [x86, x86_64]

architectures :: [String]
architectures = architecture <$> targets

findTarget :: String -> Either Error Target
findTarget arch = case List.find ((== arch) . architecture) targets of
  Nothing -> Left
    $ CommandLineError
    ("There is no target architecture called " <> red (pretty arch) <> ".")
    Nothing
    ("Available targets are: "
    <> prettyHumanList "and" (dullGreen . pretty <$> architectures)
    <> ".")
  Just t -> Right t

defaultTarget :: Target
defaultTarget = x86_64
