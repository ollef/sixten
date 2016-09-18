id : forall {a}. a -> a
id x = x

id' x = x

idT : Type {_} -> Type {_}
idT t = t

idf : forall {f a}. f a -> f a
idf x = x

const : forall {a b}. a -> b -> a
const x y = x

idConst1 : forall {f a}. f a -> f a
idConst1 x = const x (\(x : Size). x)

-- idConst2 : forall {f a}. f a -> f a
-- idConst2 x = const x (\x. x)

useConst : forall {a b}. ((a -> a -> a) -> b) -> b
useConst f = f const

APP : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
APP f x = f x

APP2 : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
APP2 f x = APP f x

app : forall {a b}. (a -> b) -> a -> b
app = APP

app2 f x = APP f x

if : Bool -> forall {n}{a : Type ~{n}}. a -> a -> a
if b = b

fun : Type {_} -> Type {1}
fun a = a -> a

if' : forall {a}. Bool -> a -> a -> a
if' b = b

Bool : Type ~{1}
Bool = forall {n} {a : Type ~{n}}. a -> a -> a

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
