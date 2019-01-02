# Sixten's query-based compiler architecture

Compilers are no longer just black boxes that take a bunch of source files and

* Incremental, meaning that if recompiling the same project after having made some changes
only needs
* They're used for tooling

[Anders Hejlsberg on modern compiler construction](https://www.youtube.com/watch?v=wSdV1M7n4gQ)

Can we 

In this post I will talk a about how this is achieved in Sixten, a functional
programming language created to experiment with giving the programmer more
control over memory layout and boxing than traditional languages do.

## Traditional pipeline-based compiler architectures

A traditional compiler pipeline might look a bit like this:

```
+-----------+            +-----+                +--------+               +--------+
|           |            |     |                |        |               |        |
|source text|---parse--->| AST |---typecheck-+->|core AST|---generate--->|assembly|
|           |            |     |       |        |        |               |        |
+-----------+            +-----+       |        +--------+               +---------
                                       |
                                       v
                               update type table
```

There are many variations, and often more steps and intermediate
representations than in the illustration, but the idea stays the same:

We push data, e.g. some source text, down a pipeline, running a fixed set of
transformations until we finally output assembly code or some other target
language. Along the way we often need to update some state. For example, we
might update a type table during type checking so we can later look up the type
of entities that the code refers to.

Traditional compiler pipelines are quite familiar to me and probably many
others, but how query-based compilers should be architected might not be as
well-known. Next I will describe one way to do it, by thinking of the compiler
as a build system.

## Build systems for compilers

The idea of mak
[Build systems à la carte](https://www.microsoft.com/en-us/research/publication/build-systems-la-carte/)

## Going from pipeline to queries

What does it take to get the type of an identifier?

```haskell
fetchType ident = do
  moduleName <- fetchModuleName ident
  parsedModule <-
```


## The Rock library

### Haxl-like semi-automatic parallelisation

### Caching

### Incremental builds by reusing state

## 
