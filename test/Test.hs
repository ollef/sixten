id : forall {a}. a -> a
id x = x

id' x = x

idT : Type -> Type
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

APP2 : forall {a b}. (forall (x : a). b x) -> forall (x : a). b x
APP2 f x = APP f x

app : forall {a b}. (a -> b) -> a -> b
app = APP

app2 f x = APP f x

app3 : forall {a b}. (a -> b) -> a -> b
app3 f x = APP f x

if : Bool -> forall {a}. a -> a -> a
if b = b

fun : Type -> Type
fun a = a -> a

if' : forall {a}. Bool -> a -> a -> a
if' b = b

Bool : Type
Bool = forall {a}. a -> a -> a

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

-- data Strategy = Eager | Lazy

-- strategize : Strategy -> Type -> Type

-- data BaseList (s : Strategy) a = Nil | Cons a (s (BaseList s a))

-- List a   = BaseList Eager a
-- Stream a = BaseList Lazy a
--
--
-- data List a = Nil | Cons a (List a)
--
-- {x = 12, y = 13} : {x : Int, y : Int} : Row Type
--
-- (x : a : A, y : b : A | ) : Row A
--
--
