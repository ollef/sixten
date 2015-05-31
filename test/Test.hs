id : forall {a}. a -> a
id x = x

const : forall {a b}. a -> b -> a
const x y = x

test : forall {f a}. f a -> f a
test x = x

{-
test2 : forall {f a}. f a -> f a
test2 x = const x (\x. x)
-- {- -}
-- -}
{-{-{--}-}{-aaaaaaa-}-}
