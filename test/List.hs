
data List a where
  Nil : List a
  Cons : a -> Ptr (List a) -> List a

deref : forall ~{t}. Ptr t -> t
deref p = case p of Ref t -> t

tail : forall ~{a}. Ptr (List a) -> Ptr (List a)
tail xs = case deref xs of
  Nil -> Ref Nil
  Cons x xs' -> xs'

map : forall {m}{n}{a : Type {m}}~{b : Type {n}}. (a -> b) -> Ptr (List a) -> Ptr (List b)
map f xs = Ref (case deref xs of
  Nil -> Nil
  Cons x xs' -> Cons (f x) (map f xs'))
