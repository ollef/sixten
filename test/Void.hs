data Unit where
  unit : Unit

data Void where

absurd : forall {a}~{A : Type {a}}. Void -> A
absurd x = case x of

loop : Unit -> Void
loop x = loop x

test = absurd (loop unit)
