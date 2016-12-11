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
