{-# LANGUAGE OverloadedStrings #-}
module Backend.Target where

import Data.Monoid
import qualified Data.List as List
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen

import Pretty

-- | The number of bits in a byte.
byteBits :: Integer
byteBits = 8

data Target = Target
  { architecture :: String
  , ptrBytes :: Integer -- ^ The number of bytes in a pointer.
  , alignBits :: Integer -- ^ How many bits to represent an alignment number.
  , ptrAlign :: Integer -- ^ The alignment of a pointer.
  } deriving (Eq, Ord, Show)

x86 :: Target
x86 = Target
  { architecture = "x86"
  , ptrBytes = 4
  , alignBits = 2
  , ptrAlign = 4
  }

x86_64 :: Target
x86_64 = Target
  { architecture = "x86-64"
  , ptrBytes = 8
  , alignBits = 2
  , ptrAlign = 8
  }

-- | The number of bits in a pointer.
ptrBits :: Target -> Integer
ptrBits t = byteBits * ptrBytes t

intBytes, intBits :: Target -> Integer
intBytes = ptrBytes
intBits = ptrBits

targets :: [Target]
targets = [x86, x86_64]

architectures :: [String]
architectures = architecture <$> targets

findTarget :: String -> Either Doc Target
findTarget arch = case List.find ((== arch) . architecture) targets of
  Nothing -> Left
    $ "There is no target architecture called "
    <> Leijen.red (pretty arch)
    <> ". Available targets are: "
    <> prettyHumanList "and" (Leijen.dullgreen . pretty <$> architectures)
    <> "."
  Just t -> Right t

defaultTarget :: Target
defaultTarget = x86_64
