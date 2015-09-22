id : forall {a}. a -> a
id x = x
-- How should we infer the type of id?
-- forall {a : Type}. a -> a
-- \{a : Type}. \(x : a). x

idT : Type -> Type
idT t = t

const : forall {a b}. a -> b -> a
const x y = x

test : forall {f a}. f a -> f a
test x = x

test2 : forall {t f a}. f a -> f a
test2 {t} x = const x (\(x : t). x)

-- test3 x = const x (\y. y)
