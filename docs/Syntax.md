# Pi types

the (List Size) [1, 2, 3]

(a : A) -> (b : B) -> c
(a : A)(b : B) -> c
forall (a : A)(b : B). c

{a : A} -> B
(a : A) -> B
{A} -> B
A -> B
A -> C

forall a. B
forall (a : A). B

How to distinguish between this and type annotations?
Remove type annotations!

# Patterns
Pi types:
```
{pat1 pat2 : Type} -> x
(pat1 pat2 : Type) -> x
Type -> x
{Type} -> x
```

Lambda and forall:
```
\{pat1 pat2 : Type}. x
\(pat1 pat2 : Type). x
\pat1 pat2. x
\{pat1} {pat2}. x
```

Cases:
```
case x of
  pat1 -> x
```

# Records

record {x = a, y = b} : record {x : A, y : B x)
Rows
record {x = a, y = b | r} : record {x : A, y : B | R}
Implicit params
{x : A}

# Do notation

Don't use `<-`, instead have `!_` syntax and `=`:

f = do
  x = !monadic
  y = nonMonadic
  pure (x + y)

```
do
  f !x !y
==>
x >>= \xres ->
y >>= \yres ->
f xres yres
```

we can emulate lets with pure dos:

```
  f = do
    x = 123
    y = 243
    x + y
```

# Type classes

class Eq (A : Type) where
  eq : A -> A -> Bool
