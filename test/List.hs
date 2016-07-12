deref : forall {n}~{t : Type {n}}. Ptr t -> t
deref p = case p of Ref t -> t

data List a where
  Nil : List a
  Cons : a -> Ptr (List a) -> List a

tail : forall ~{a}. Ptr (List a) -> Ptr (List a)
tail xs = case deref xs of
  Nil -> xs
  Cons x xs' -> xs'

map : forall {m}{n}~{a : Type {m}}~{b : Type {n}}. (a -> b) -> Ptr (List a) -> Ptr (List b)
map f xs = Ref (case deref xs of
  Nil -> Nil
  Cons x xs' -> Cons (f x) (map f xs'))

testList : Ptr (List Size)
testList = Ref (Cons 1 (Ref (Cons 2 (Ref Nil))))

mappedList : Ptr (List Size)
mappedList = map (addSize 1) testList

testList2 : List Size
testList2 = deref testList
