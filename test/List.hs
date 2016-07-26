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
testList = Ref (Cons 1 (Ref (Cons 2 (Ref (Cons 3 (Ref Nil))))))

mappedList : Ptr (List Size)
mappedList = map (addSize 1) testList

testList2 : List Size
testList2 = deref testList

add3 : Size -> Size -> Size -> Size
add3 a b c = addSize (addSize a b) c

sum : Ptr (List Size) -> Size
sum xs = case deref xs of
  Nil -> 0
  Cons x xs' -> addSize x (sum xs')

mappedList2 = map (add3 1) testList
mappedList3 = map (\f. f 10) mappedList2

printSum = printSize (sum testList)
printMappedSum = printSize (sum mappedList)
printMappedSum2 = printSize (sum mappedList3)
