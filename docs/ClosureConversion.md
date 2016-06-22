Basic idea:

```
cc f = CL f0 n
cc (f e1 .. em)
  | m == n = f e1 .. em
  | m < n = CL fm (n - m) e1 .. em
  | m > n = apply (m - n) (f e1 .. en) en+1 .. em
cc (x e1 .. em) = applym x e1 .. em

fm xthis xm+1 .. xn = case xthis of
  CL _ _ y1 .. ym -> f y1 .. ym xm+1 .. xn

applym xthis x1 .. xm = case xthis of
  CL funknown n
    | m == n -> funknown xthis x1 .. xm
    | m < n -> CL pap(n-m),m (n - m) xthis x1 .. xm
    | m > n -> apply(m-n) (funknown xthis x1 .. xn) xn+1 .. xm

papk,m xthis x1 .. xk = case xthis of
  CL _ _ ythat y1 .. ym -> apply(m+k) ythat y1 .. ym x1 .. xk
```

Size handling

* option 1 (indirect): copy all args to unknown functions to the heap

```
cc f = CL f0 n
cc (f e1 .. em)
  | m == n = f e1 .. em
  | m < n = CL fm (n - m) (Ref e1) .. (Ref em)
  | m > n = apply (m - n) (f e1 .. en) (Ref en+1) .. (Ref em)
cc (x e1 .. em) = applym x (Ref e1) .. (Ref em)

fm xthis xm+1 .. xn = case xthis of
  CL _ _ y1 .. ym -> f (deref y1) .. (deref ym) (deref xm+1) .. (deref xn)

applym xthis x1 .. xm = case xthis of
  CL funknown n
    | m == n -> funknown xthis x1 .. xm
    | m < n -> CL pap(n-m),m (n - m) xthis x1 .. xm
    | m > n -> apply(m-n) (funknown xthis x1 .. xn) xn+1 .. xm

papk,m xthis x1 .. xk = case xthis of
  CL _ _ ythat y1 .. ym -> apply(m+k) ythat y1 .. ym x1 .. xk
```

* option 2 (size passing): add extra size arguments to applym, CL, and pap

```
cc f = CL f0 n
cc (f e1 .. em)
  | m == n = f e1 .. em
  | m < n = Ref (CL fm (n - m) e1 .. em)
  | m > n = apply (m - n) (f e1 .. en) sizeof(en+1) .. sizeof(em) en+1 .. em
cc (x e1 .. em) = applym x sizeof(e1) .. sizeof(em) e1 .. em

fm xthis xm+1size .. xnsize xm+1 .. xn = case deref xthis of
  CL _ _ y1 .. ym -> f y1 .. ym xm+1 .. xn

applym xthis x1size .. xmsize x1 .. xm = case deref xthis of
  CL funknown n
    | m == n -> funknown xthis x1size .. xmsize x1 .. xm
    | m < n -> Ref (CL pap(n-m),m (n - m) xthis x1size .. xmsize x1 .. xm)
    | m > n -> apply(m-n) (funknown xthis x1size .. xnsize x1 .. xn) xn+1size .. xmsize xn+1 .. xm

papk,m xthis x1size .. xksize x1 .. xk = case deref xthis of
  CL _ _ ythat y1size .. ymsize y1 .. ym -> apply(m+k) ythat y1size .. ymsize x1size .. xksize y1 .. ym x1 .. xk
```

* option 3 (hybrid): construct fm by copy, but copy unknown args
* option 4 (array): pass all args to apply as stack array

```
cc f = CL f0 n
cc (f e1 .. em)
  | m == n = f e1 .. em
  | m < n = Ref (CL fm (n - m) e1 .. em)
  | m > n = apply(m - n) (f e1 .. en) (Args en+1 .. em)
cc (x e1 .. em) = applym x (Args e1 .. em)

fm xthis argsSize args =
  case deref xthis of
    CL _ _ y1 .. ym -> case args of
      Args xm+1 .. xn -> f y1 .. ym xm+1 xn

applym xthis argsSize args = case deref xthis of
  CL funknown n
    | m == n -> funknown xthis args
    | m < n -> Ref (CL pap(n-m),m (n - m) xthis argsSize args)
    | m > n -> apply(m-n) (funknown xthis argsSize args) ??

papk,m xthis args2Size args2 = case deref xthis of
  CL _ _ ythat argsSize args -> apply(m+k) ythat y1size .. ymsize x1size .. xksize y1 .. ym x1 .. xk
```
