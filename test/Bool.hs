-- TODO what to do with this?
--
-- generalisation adds lambda to the type which makes TC go wrong
-- fully specifying the type of {a} is a fix.
--
-- Should generalisation generalise vars found in expressions?
Bool : Type {1}
Bool = forall {A : Type {0}}. forall {a : A}. a -> a -> a
-- Bool = forall {a : A}. a -> a -> a

True : Bool
True x y = x
