id : forall {a}. a -> a
id x = x
-- How should we infer the type of id?
-- forall {a : Type}. a -> a
-- \{a : Type}. \(x : a). x
id' x = x

idT : Type -> Type
idT t = t

const : forall {a b}. a -> b -> a
const x y = x

test : forall {f a}. f a -> f a
test x = x

test2 : forall {t f a}. f a -> f a
test2 {t} x = const x (\(x : t). x)

APP : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
APP f x = f x

app : forall {a b}. (a -> b) -> a -> b
app = APP

-- test3 f x = app f x
