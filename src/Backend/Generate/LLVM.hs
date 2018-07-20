module Backend.Generate.LLVM where

import LLVM.AST.Instruction
import LLVM.IRBuilder
import LLVM.IRBuilder.Internal.SnocList

import Syntax.Name
import Syntax.NameHint

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

hinted :: MonadIRBuilder m => m a -> NameHint -> m a
hinted gen NoHint = gen
hinted gen (NameHint n) = gen `named` fromName n
