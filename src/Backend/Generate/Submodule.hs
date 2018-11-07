module Backend.Generate.Submodule where

import Protolude

import Data.HashMap.Lazy(HashMap)
import qualified LLVM.AST as LLVM

import Syntax.Extern(Language)
import Syntax

data Submodule = Submodule
  { declarations :: !(HashMap GName [LLVM.Definition])
  , definitions :: [LLVM.Definition]
  , initCode :: Maybe LLVM.Operand
  , externs :: [(Language, Text)]
  }

