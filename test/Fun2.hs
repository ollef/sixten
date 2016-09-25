Bool : Type {1}
Bool = forall {a : Type {1}}. a -> a -> a

False : Bool
False x y = y

if : forall {a}. Bool -> a -> a -> a
if b = b

and : Bool -> Bool -> Bool
and b1 b2 = if b1 b2 False
