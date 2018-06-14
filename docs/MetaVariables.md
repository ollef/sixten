# Metavariables

Metavariables (or flexible/unification variables) are used during
type-checking to stand for an unknown term or type that is later filled in by
unification or generalisation.

This means that we have two kinds of variables during type-checking, namely
ordinary free variables or universals, e.g. when type-checking inside a lambda
or pi, and metavariables.

## Scopes

We need to be careful with scopes when dealing with metavariables, because
the scope can be different at each of its occurrence sites. Consider for example
the meta variable `m` of type `M` in the following code:

```
t1 = \(x : X). f m
t2 = \(y : Y). g m
```

When type-checking `t1`, we might end up in a situation where we want to solve `m` to
some term that mentions `x`, i.e. `m = ... x ...`. However, this would mean that `t2`
suddenly has an unbound variable, `x`. We shouldn't allow this.

To fix this, we encode the scope in the metavariable itself by parameterising
it by the local context when it's created.

So if `m` is created during type-checking of `t1`, we don't give it type `m :
M`, but `m : (x : X) -> M`, and apply it to the local variables in context,
yielding instead:

```
t1 = \(x : X). f (m x)
```

This is in line with what Agda does, and [Abel and Pientka's paper on
dependently typed unification][1].

## Unification

Unification means making two term equal by filling in metavariables. During
unification, we traverse the two terms simultaneously, and when we encounter a
situation like

```
unify m t
```

we solve `m = t`.

With metavariables that are parameterised by their local context, this gets
trickier, because we might have the following situation:

```
unify (m xs) t
```

where `xs` is a list of arguments given to `m`.

We can then use Miller pattern unification, which applies if `xs` is a list
of distinct universally quantified variables, and says that `m = \xs. t` is then a
most general solution to the problem.

We also use _pruning_ from the [aforementioned paper][1].

## Generalisation

We also make use of metavariables when generalising definitions. For example,
given the definition

```
id x = x
```

the type-checker will create a metavariable `m` for the type of `x`, since it's unknown,
yielding type `id : m -> m`. To generalise `id`, we replace all metavariables
with universally quantified variables, yielding `id : forall x. x -> x`.

## References

[1]: [Andreas Abel and Brigitte Pientka: Higher-Order Dynamic Pattern Unification for Dependent Types and Records](http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf)
