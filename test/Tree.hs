data Tree a where
  Leaf : a -> Tree a
  Fork : Ptr (Tree a) -> Ptr (Tree a) -> Tree a

deref : forall {n}{a : Type {n}}. Ptr a -> a
deref p = case p of Ref x -> x

mapTree : forall {a b}. (a -> b) -> Ptr (Tree a) -> Ptr (Tree b)
mapTree f tree = Ref (case deref tree of
  Leaf a -> Leaf (f a)
  Fork t1 t2 -> Fork (mapTree f t1) (mapTree f t2))
