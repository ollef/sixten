module Backend.Generate.LLVM where

import Control.Monad.State
import IRBuilder
import qualified LLVM.AST as LLVM
import LLVM.AST.Instruction
import Util.SnocList

import Syntax.Hint
import Syntax.Name

with
  :: MonadIRBuilder m
  => m a
  -> (Instruction -> Instruction)
  -> m a
with ma f = do
  result <- ma
  modifyBlock $ \bb -> bb
    { partialBlockInstrs = case partialBlockInstrs bb of
      SnocList (nm := i:is) -> SnocList (nm := f i : is)
      SnocList (Do i:is) -> SnocList (Do (f i) : is)
      is -> is
    }
  return result

currentBlock :: MonadIRBuilder m => m LLVM.Name
currentBlock
  = liftIRState
  $ gets
  $ maybe (LLVM.UnName 0) partialBlockName . builderBlock

hinted :: MonadIRBuilder m => m a -> NameHint -> m a
hinted gen (NameHint (Hint Nothing)) = gen
hinted gen (NameHint (Hint (Just n))) = gen `named` fromName n
