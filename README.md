Sixten

```
     o
 ,---.-. ,-|- ,--.--.
 `---|  |  |  |--'  |
 `---'-' `-'--`--'  `-'
```

======

Functional programming without indirections.

Introduction
------------

Most high-level languages with parametrically polymorphic (or generic) data
types and functions, even if it is offered under a different name like
templates, fall into one of the following two categories:

1.  They use a uniform representation for polymorphic data, which is usually
    word-sized. If the data is bigger than a word it has to be represented as
    a pointer to the data.

2.  They use template instantiation, meaning that new code is generated when a
    polymorphic function is used at a new type.

Neither of these approaches are perfect: With the uniform representation
approach we lose control over how our data is laid out in memory, and with the
template instantiation approach we lose modularity:

1.  With a uniform representation we cannot for example define polymorphic
    intrusive linked lists, where the node data is stored next to the list's
    "next pointer". Given the list definition

    ```
    data List a = Nil | Cons a (List a)
    ```

    The representation in memory of the list `Cons x (Cons y Nil)`, is
    something like:

    ```
         [x]           [y]
          ^             ^
          |             |
    [Cons * *]--->[Cons * *]--->[Nil]
    ```

    We cannot define a polymorphic list whose representation is intrusive:

    ```
    [Cons x *]--->[Cons y *]--->[Nil]
    ```

    What we gain from using a uniform representation is modularity: A
    polymorphic function, say `map : (a -> b) -> List a -> List b`, can be
    compiled once and used for any types `a` and `b`.

2.  With templates, we are able to define intrusive lists, like in the following
    C++-like code:

    ```
    template<typename A>
    class List
    {
      A element;
      List<A>* next;
    }
    ```

    However, unless we know all the types that `A` will be instantiated with in
    advance, we have to generate new code for every instantiation of the
    function, meaning that we have lost modularity. Template instantiation also
    leads to bigger code since it generates multiple versions of the same
    function.

    What is gained is the ability to more finely express how our data is laid
    out in memory, which for instance means that we can write code that is
    cache-aware and which uses fewer memory allocation.

Sixten gives us the best of both worlds. It gives us the expressivity to define
polymorphic intrusive lists and functions on them while retaining modularity.
The novel feature that allows this is _size polymorphism_.

The definition of the list type in Sixten is

```
data List a = Nil | Cons a (Ptr (List a))
```

The difference between Sixten and (for instance) Haskell is that everything is
unboxed by default, meaning that the `a` field in the `Cons` constructor is not
represented by a pointer to an `a`, but it _is_ an `a`. This also means that we
have to mark where we actually want pointers with the `Ptr` type constructor.
The `Cons` constructor has to hold a _pointer to_ the tail of the list because
we would otherwise create an infinite-size datatype, which is not allowed in
Sixten.
