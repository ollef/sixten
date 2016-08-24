data Tuple {a b : Size} (A : Type {a}) (B : Type {b}) where
  Tup : A -> B -> Tuple A B

fst : forall ~{a b}. Tuple a b -> a
fst x = case x of
  Tup a b -> a

snd : forall ~{a b}. Tuple a b -> b
snd x = case x of
  Tup a b -> b

complex : Tuple Size Size
complex = Tup 10 20

test : Size
test = printSize (addSize (fst complex) (snd complex))
