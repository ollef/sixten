id : forall {a}. a -> a
id x = x

const : forall {a b}. a -> b -> a
const x y = x
