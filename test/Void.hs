data Unit where
  unit : Unit

data Void where

absurd : forall ~{A : Type {_}}. Void -> A
absurd x = case x of

loop : Unit -> Void
loop x = loop x

test = absurd (loop unit)
