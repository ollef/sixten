data Unit where
  unit : Unit

data Void where

absurd : forall ~{A : Type {_}}. Void -> A
absurd x = case x of

loop : Unit -> Void
loop x = loop x

test = absurd (loop unit)

const x y = x

loop2 : Unit -> Void
loop2 = (\l. \x. const l l x) (\x. loop x)
