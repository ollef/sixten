deref : forall {n}{t : Type {n}}. Ptr t -> t
deref p = case p of Ref t -> t

data List {a : Size}(A : Type {a}) where
  Nil : List A
  Cons : A -> Ptr (List A) -> List A

data List2 (A : Type) where
  Nil2 : List2 A
  Cons2 : A -> Ptr (List2 A) -> List2 A

tail : forall {A : Type}. Ptr (List A) -> Ptr (List A)
tail xs = case deref xs of
  Cons x xs' -> xs'
  Nil -> xs

tail2 xs = case deref xs of
  Cons x xs' -> xs'
  Nil -> xs

tail3 : forall {A}. Ptr (List A) -> Ptr (List A)
tail3 xs = case deref xs of
  Cons x xs' -> xs'
  Nil -> xs

map : forall {m}{n}{a : Type {m}}{b : Type {n}}. (a -> b) -> Ptr (List a) -> Ptr (List b)
map f xs = Ref (case deref xs of
  Nil -> Nil
  Cons x xs' -> Cons (f x) (map f xs'))

map2 f xs = Ref (case deref xs of
  Nil -> Nil
  Cons x xs' -> Cons (f x) (map2 f xs'))

map3 f xs = case deref xs of
  Cons x xs' -> Ref (Cons (f x) (map2 f xs'))
  Nil -> Ref Nil

sizeof : forall {n}. (Type {n}) -> Size
sizeof {n} _ = n

sizeOfList = printSize (sizeof (List (List Size)))

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
print2 = printSize (sum (map (\f. f 2) (map (add3 1) testList)))
print3 = printSize (sum (map (\f. f 2) (map (\f. f 1) (map add3 testList))))

-- mappedList2 = map (add3 2) testList
-- mappedList3 = map (\f. f 3) mappedList2

-- printSum = printSize (sum testList)
-- printMappedSum = printSize (sum mappedList)
-- printNum = printSize (add3 1 2 3)
-- printMappedSum2 = printSize (sum mappedList3)
