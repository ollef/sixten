deref : forall {n}~{t : Type {n}}. Ptr t -> t
deref p = case p of Ref t -> t

data List {a : Size}(A : Type {a}) where
  Nil : List A
  Cons : A -> Ptr (List A) -> List A

tail : forall ~{a}. Ptr (List a) -> Ptr (List a)
tail xs = case deref xs of
  Nil -> xs
  Cons x xs' -> xs'

map : forall {m}{n}~{a : Type {m}}~{b : Type {n}}. (a -> b) -> Ptr (List a) -> Ptr (List b)
map f xs = Ref (case deref xs of
  Nil -> Nil
  Cons x xs' -> Cons (f x) (map f xs'))

-- mappedList : Ptr (List Size)
-- mappedList = map (addSize 1) testList

testList : Ptr (List Size)
testList = Ref (Cons 1 (Ref (Cons 2 (Ref (Cons 3 (Ref Nil))))))

testList2 : List Size
testList2 = deref testList

add3 : Size -> Size -> Size -> Size
add3 a b c = addSize (addSize a b) c

sum : Ptr (List Size) -> Size
sum xs = case deref xs of
  Nil -> 0
  Cons x xs' -> addSize x (sum xs')

print1 = printSize (sum (map (add3 1 2) testList))
print2 = printSize (sum (map (\(f : Size -> Size). f 2) (map (add3 1) testList)))
print3 = printSize (sum (map (\(f : Size -> Size). f 2) (map (\(f : Size -> Size -> Size). f 1) (map add3 testList))))

-- mappedList2 = map (add3 2) testList
-- mappedList3 = map (\f. f 3) mappedList2

-- printSum = printSize (sum testList)
-- printMappedSum = printSize (sum mappedList)
-- printNum = printSize (add3 1 2 3)
-- printMappedSum2 = printSize (sum mappedList3)
