id : forall {a}. a -> a
id x = x

id' x = x

idT : Type {_} -> Type {_}
idT t = t

idf : forall {f a}. f a -> f a
idf x = x

const : forall {a b}. a -> b -> a
const x y = x

idConst : forall {t f a}. f a -> f a
idConst {t} x = const x (\(x : t). x)

useConst : forall {a b}. ((a -> a -> a) -> b) -> b
useConst f = f const

APP : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
APP f x = f x

-- TODO
--
-- APP2 : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
-- APP2 f x = APP f x

-- app : forall {a b}. (a -> b) -> a -> b
-- app = APP

-- app2 f x = APP f x

if : Bool -> forall {n}{a : Type {n}}. a -> a -> a
if b = b

fun : Type {_} -> Type {1}
fun a = a -> a

if' : forall {a}. Bool -> a -> a -> a
if' b = b

Bool : Type {1}
Bool = forall {n} {a : Type {n}}. a -> a -> a

True : Bool
True x y = x

False : Bool
False x y = y

a : forall {a}. a
a = a

and : Bool -> Bool -> Bool
and b1 b2 = if' b1 b2 False

or : Bool -> Bool -> Bool
or b1 b2 = if' b1 True b2
