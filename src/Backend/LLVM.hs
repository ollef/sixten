module Backend.LLVM where

import IRBuilder
import LLVM.AST.Instruction
import Util.SnocList

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
