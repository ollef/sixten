# Sixten's query-based compiler architecture

Compilers are no longer just black boxes that take a bunch of source files and produce assembly code. We expect them to:

* Be incremental, meaning that if we recompile a project after having made a few changes we only recompile what is affected by the changes.
* Provide tooling such as language servers, supporting functionality like going to definition, finding the type of the expression at a specific location, and showing error messages on the fly.

This is what Anders Hejlsberg talks about in
[his video on modern compiler construction](https://www.youtube.com/watch?v=wSdV1M7n4gQ)
that some of you might have seen.

In this document I will talk a about how this is achieved in Sixten, an
experimental functional programming language created to give the programmer
more control over memory layout and boxing than traditional languages do.

## Traditional pipeline-based compiler architectures

A traditional compiler pipeline might look a bit like this:

```
+-----------+            +-----+                +--------+               +--------+
|           |            |     |                |        |               |        |
|source text|---parse--->| AST |---typecheck-+->|core AST|---generate--->|assembly|
|           |            |     |       ^        |        |               |        |
+-----------+            +-----+       |        +--------+               +---------
                                       |
                                 read and write
                                     types
                                       |
                                       v
                                  +----------+
                                  |          |
                                  |type table|
                                  |          |
                                  +----------+
```

There are many variations, and often more steps and intermediate
representations than in the illustration, but the idea stays the same:

We push source text, down a pipeline, running a fixed set of transformations
until we finally output assembly code or some other target language. Along the
way we often need to read and update some state. For example, we might update a
type table during type checking so we can later look up the type of entities
that the code refers to.

Traditional compiler pipelines are quite familiar to me and probably many
others, but how query-based compilers should be architected might not be as
well-known. I will describe one way to do it, by thinking of the compiler as a
build system.

## Build systems for compilers

TODO

[Build systems à la carte](https://www.microsoft.com/en-us/research/publication/build-systems-la-carte/)

## Going from pipeline to queries

What does it take to get the type of a qualified name, such as `Data.List.map`?
In a pipeline-based architecture we would just look it up in the type table.
With queries, we have to think a bit differently. Instead of relying on having
updated some piece of state, we do it almost as if it was done from scratch.

As a first iteration, we do it completely from scratch. It might look a little bit like this:

```haskell
fetchType :: QName -> Type
fetchType (QName moduleName name) = do
  fileName <- moduleFileName moduleName
  sourceCode <- readFile fileName
  parsedModule <- parseModule sourceCode
  resolvedModule <- resolveNames parsedModule
  let definition = lookup name resolvedModule
  inferDefinitionType definition
```

We first find out what file the name comes from (that might be `Data/List.hs`
for `Data.List`), then read the contents of the file, parse it, perhaps we do
name resolution to find out what the names in the code refer to given what is
imported, and lastly we look up the name-resolved definition and type check it,
returning its type.e

All this for just for getting the type of an identifier? It's obviously quite
ridiculous because looking up the type of a name is something we'll do loads of
times during the type checking of a module. We're not done yet though.

Let's first refactor the code into smaller functions:

```haskell
fetchParsedModule :: ModuleName -> ParsedModule
fetchParsedModule moduleName = do
  fileName <- moduleFileName moduleName
  sourceCode <- readFile fileName
  parseModule moduleName

fetchResolvedModule :: ModuleName -> ParsedModule
fetchResolvedModule moduleName = do
  parsedModule <- fetchParsedModule moduleName
  resolveNames parsedModule

fetchType :: QName -> Type
fetchType (QName moduleName name) = do
  resolvedModule <- fetchResolvedModule moduleName
  let definition = lookup name resolvedModule
  inferDefinitionType definition
```

Note that each of the functions do almost everything from scratch on their own.

Next, we'll 

## The Rock library

### Dependent queries

### Haxl-like semi-automatic parallelisation

### Caching

### Incremental builds by reusing state

#
