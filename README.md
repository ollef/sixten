# Sixten [![Build Status](https://travis-ci.org/ollef/sixten.svg?branch=master)](https://travis-ci.org/ollef/sixten) [![Gitter chat](https://badges.gitter.im/ollef/sixten.png)](https://gitter.im/sixten-lang)

```
     o
 ,---.-. ,-|- ,--.--.
 `---|  |  |  |--'  |
 `---'-' `-'--`--'  `-'
```

Sixten is an experimental functional programming language where all data is
unboxed by default. Functional programming with fewer indirections!

Below follow some of Sixten's features that work now.

### Unboxed stack- or heap-allocated data types

We can define a new type of tuples of two given types as:

```haskell
type Pair a b = MkPair a b
```

We can then use the constructor `MkPair` to construct a pair. As an example,
`MkPair 610 "Sixten"` has type `Pair Int String`.

The size in memory of `Pair a b` is the size of `a` plus the size of `b`, and
the pair is passed in registers or on the stack when used in a function.

On a 64-bit machine, `sizeOf Int = 8` and `sizeOf (Pair Int Int) = 16`.

_Nested_ pairs are also laid out flat in memory: `sizeOf (Pair Int (Pair Int Int)) = 24`.

With this in mind we can define stack-allocated, flat, unboxed vectors of a
given number of elements as:

```haskell
Vector : Nat -> Type -> Type
Vector Zero _ = Unit
Vector (Succ n) a = Pair a (Vector n a)
```

Here, `Unit` is the zero-size type with one inhabitant, and `Pair A B`
the type of unboxed pairs of `A` and `B`.

Here's a function that sums a vector of ints:

```haskell
sum : (n : Nat) -> Vector n Int -> Int
sum Zero MkUnit = 0
sum (Succ n) (MkPair x xs) = addInt x (sum n xs)
```

The type of heap-allocated vectors is then `Ptr (Vector n a)`, where `Ptr`
is a built-in type of type `Type -> Type` which returns a boxed version of
the argument. For any type `t`, `sizeOf (Ptr t) = 8` on a 64-bit machine.
Using `Ptr` we can define (immutable) arrays, where the length is not visible
in the type, as:

```haskell
type Array a where
  MkArray : (n : Nat) -> Ptr (Vector n a) -> Array a
```

Another example where `Ptr` can be used is to define a type of linked lists:

```haskell
type List a = Nil | Cons a (Ptr (List a))
```

Here `Ptr` makes it explicit that a `Cons` cell has a _pointer to_ a list.
Note that the `a` is unpacked in `Cons` (unless it's a `Ptr something`),
so it's an _intrusive_ linked list where the tail pointer is next to the
`a` element in memory.

### Algebraic data types and pattern matching

There are two ways to define algebraic data types:

- ADT-style:

```haskell
type Maybe a = Nothing | Just a
```

- GADT-style:

```haskell
type Maybe a where
  Nothing : Maybe a
  Just : a -> Maybe a
```

Pattern matching can be done in clauses and case expressions:

```haskell
fromMaybe : forall a. a -> Maybe a -> a
fromMaybe def Nothing = def
fromMaybe _ (Just x) = x
```

```haskell
fromMaybe' : forall a. a -> Maybe a -> a
fromMaybe' def mx = case mx of
  Nothing -> def
  Just x -> x
```

In memory, algebraic data types are represented by an integer tag next to a
chunk of memory big enough to hold the contents of any of the constructors.
If the type has fewer than two constructors it's represented without a tag.

This means that `type Unit = MkUnit` has size zero, and `Maybe A` has size
`tagSize + sizeOf A`.

### Implicit parameters

The `forall` keyword introduces implicit parameters in a type:

```haskell
id : forall a. a -> a
id x = x
```

Implicit arguments are inferred by usage, so `a = Int` in `id 610`.  They
can also be explicitly specified using `@`: `id @Int 610`.

### Dependent function types (pi types)

The arguments in function types can be named and used in the return type:

```haskell
sum : (n : Nat) -> Vector n Int -> Int
```

### Inductive families (GADTs)

Constructors can constrain their type's parameters. For instance, we can define
propositional equality as follows:

```haskell
type Equals a b where
  Refl : Equals a a
```

Here, the `Refl` constructor can only be used when the two parameters to
`Equals` are equal. When given a value of type `Equals a b`, we can use pattern
matching to reveal the constraint that `a` and `b` are equal. As an example,
here's how to define transitivity:

```haskell
trans : forall a b c. Equals a b -> Equals b c -> Equals a c
trans Refl Refl = Refl
```

### Type inference

Sixten's type inference is inspired by
[Practical type inference for arbitrary-rank types](https://www.microsoft.com/en-us/research/publication/practical-type-inference-for-arbitrary-rank-types/).

### Classes

These are similar to Haskell's type classes.

As an example, here's how to define a `Functor` class:

```haskell
class Functor f where
  map : forall a b. (a -> b) -> f a -> f b

type Maybe a = Nothing | Just a

instance Functor Maybe where
  map _ Nothing = Nothing
  map f (Just x) = Just (f x)
```

### Extern C code/FFI

Extern C code can be written in `(C| ... |)` blocks. Sixten expressions can be
spliced into the code with `$expr`. For example, here's how addition on the
built-in type `Int` can be defined:

```haskell
addInt : Int -> Int -> Int
addInt x y = (C|
  return $x + $y;
|)
```

Extern C code blocks are compiled to C functions which are compiled separately.
LLVM link-time optimisation is used to minimise function-call overheads.

### Compilation to LLVM

This currently uses the Boehm–Demers–Weiser garbage collector for
garbage-collecting heap-allocated data.

### Boxed types

Sometimes we do want boxed types, e.g. to define linked lists without having to
explicitly wrap and unwrap values in `Ptr`s. This can be done with the `boxed`
keyword:

```haskell
boxed
type List a = Nil | Cons a (List a)
```

This means that all values of type `List t` are indirected through a pointer,
as if using `Ptr (List t)`.

The `Ptr` type from the `Builtin` module is defined using `boxed`:

```haskell
boxed
type Ptr a = Ref a
```

## Planned features

* Records
* Effects and IO
* Standard library
* Infix and/or mixfix definitions
* Dedicated garbage collector

See the issues list for more details about what's planned.

## Compared to other languages

Sixten is very related to other functional languages such as Haskell, Agda, and
Idris. The biggest difference between other languages and Sixten is the way
that Sixten allows us to control the memory layout of data.

Most high-level languages with parametrically polymorphic (or generic) data
types and functions, even if it is offered under a different name like
templates, fall into one of the following two categories:

1.  They use a uniform representation for polymorphic data, which is usually
    word-sized. If the data is bigger than a word it's represented as a pointer
    to the data.

2.  They use monomorphisation or template instantiation, meaning that new code
    is generated statically whenever a polymorphic function is used at a new
    type.

Neither of these approaches is perfect: With the uniform representation
approach we lose control over how our data is laid out in memory, and with the
template instantiation approach we lose modularity and polymorphic recursion:

With a uniform representation we cannot for example define polymorphic
intrusive linked lists, where the node data is stored next to the list's
"next pointer". Given the (Haskell) list definition

```haskell
data List a = Nil | Cons a (List a)
```

The representation in memory of the list `Cons x (Cons y Nil)` in languages
with a uniform representation is something like:

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
polymorphic function, say `map : forall a b. (a -> b) -> List a -> List b`, can be
compiled once and used for any types `a` and `b`.

With monomorphisation, we are able to define intrusive lists, like in the
following C++-like code:

```c++
template<typename A>
class List
{
  A element;
  List<A>* next;
}
```

However, unless we know all the types that `A` will be instantiated with in
advance, we have to generate new code for every instantiation of the
function, meaning that we have partly lost modular compilation. We also
can't have polymorphic recursion since that would require an unbounded
number of instantiations. Template instantiation also leads to bigger code
since it generates multiple versions of the same function.

What is gained is the ability to more finely express how our data is laid
out in memory, which for instance means that we can write code that is
cache-aware and which uses fewer memory allocations.

Sixten gives us both: it allows us to control the memory layout of our data
all the while retaining modularity.

The definition of the list type in Sixten is

```haskell
type List a = Nil | Cons a (Ptr (List a))
```

The difference between Sixten and (for instance) Haskell is that everything is
unboxed by default, meaning that the `a` field in the `Cons` constructor is not
represented by a pointer to an `a`, but it _is_ an `a`. This also means that we
have to mark where we actually want pointers with the `Ptr` type constructor.
The `Cons` constructor has to hold a _pointer to_ the tail of the list because
we would otherwise create an infinite-size datatype, which is not allowed in
Sixten.

The novel feature that allows this is _type representation polymorphism_.
Types are compiled to their representation in Sixten. In the current
implementation of Sixten the representation consists only of the type's size in
memory, so e.g. `Int` is compiled to the integer `8` on a 64-bit system.  A
polymorphic function like `map : forall a b. (a -> b) -> List a -> List b`
implicitly takes the types `a` and `b` as arguments at runtime, and its
compiled form makes use of the type representation information to calculate
the memory offsets and sizes of its arguments and results that are needed to
be representation polymorphic.

This kind of polymorphism is potentially slower than specialised functions
since it passes around additional implicit arguments and does more calculation
at runtime. Some of this inefficiency should be offset by having better memory
layout than systems using uniform representations, meaning better cache
behaviour. Also note that type representation polymorphism does not preclude
creating specialised versions of functions known to be performance-critical,
meaning that we can choose to use monomorphisation when we want to.

Sixten's type representation polymorphism is closely related to research on
_intensional polymorphism_. What sets Sixten apart is the way type
representations are used in the compiled code. Sixten doesn't need to use type
representations to perform code selection, but rather compiles polymorphic
functions to _single_ implementations that leverage the information in the
type representation to be general enough to work for all types.
Type representations are also not structural in Sixten, but consist simply
of the size of the type.

## Installation

To build Sixten from source, clone this repository and build it using
[Stack](https://www.haskellstack.org):

     git clone git@github.com:ollef/sixten.git
     cd sixten
     stack build

To install the `sixten` binary, run:

     stack install

This will install `sixten` locally, which usually means `~/.local/bin`. This
path can be added to your `PATH` environment variable if desired.

To run tests, run:

     stack test

### Sixten compilation dependencies

To build Sixten programs, you'll need:

* LLVM and Clang 6. The `--llvm-config` flag can be used to tell `sixten` where
  to look for these.
* The Boehm–Demers–Weiser garbage collector library.
* pkg-config (used to find the Boehm–Demers–Weiser GC library).

### Editor integration

#### Language server

The compiler has a work-in-progress language server.

To install it, set up your editor's language client to use the command
`sixten language-server`.

The language server currently has the following limitations:

* Only diagnostic reporting and hovering is supported.
* Hovering only works in certain contexts.
* Only single file projects are supported.
* Everything is recompiled on each save.

#### Vim

Here's how to set up Sixten with
[LanguageClient-neovim](https://github.com/autozimu/LanguageClient-neovim/)
using
[vim-plug](https://github.com/junegunn/vim-plug):
:


```viml
Plug 'autozimu/LanguageClient-neovim', {
  \ 'branch': 'next',
  \ 'do': './install.sh'
  \ }

let g:LanguageClient_serverCommands = {
  \ 'sixten': ['~/.local/bin/sixten', 'language-server']
  \ }
```

The above assumes that the `sixten` binary is installed locally in
`~/.local/bin`.

There are syntax highlighting definitions in the `vim` directory of the
repository. To install it using
[vim-plug](https://github.com/junegunn/vim-plug), use:

```viml
Plug 'ollef/sixten', { 'rtp': 'vim' }
```

### Bash command completion

With `sixten` in your PATH, add the following to your `.bashrc` to get
completion for the `sixten` command:

```shell
source <(sixten --bash-completion-script `which sixten`)
```
## Changelog

[Here](CHANGELOG.md).

## Contributions

Does this sound interesting to you? Get involved and help shape the Sixten
language! Contributions are always welcome.

If want to get in touch, create a Github issue or join the [Gitter chat](https://gitter.im/sixten-lang).

Please read the [code of conduct](CODE_OF_CONDUCT.md).

## Contributors

[Olle Fredriksson](https://github.com/ollef)

[Victor Borja](https://github.com/vic)

[Varun Gandhi](https://github.com/theindigamer)

[Brandon Hamilton](https://github.com/brandonhamilton)

[He Tao](https://github.com/sighingnow)

[Dan Rosén](https://github.com/danr)
