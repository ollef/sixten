data Tree a where
  Leaf : a -> Tree a
  Fork : Ptr (Tree a) -> Ptr (Tree a) -> Tree a

deref : forall {n}~{a : Type {n}}. Ptr a -> a
deref p = case p of Ref x -> x

mapTree : forall ~{a b}. (a -> b) -> Tree a -> Tree b
mapTree f tree = case tree of
  Leaf a -> Leaf (f a)
  Fork t1 t2 -> Fork (Ref (mapTree f (deref t1))) (Ref (mapTree f (deref t2)))
