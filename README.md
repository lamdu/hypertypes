# syntax-tree

`syntax-tree` is a Haskell library that can be described in several ways:

* [`recursion-schemes`](https://github.com/ekmett/recursion-schemes/), super-powered
* Tools for indexed indices
* A library for representing and processing mutually recursive syntax trees via indexed variants of `Functor` and other classes

Like `recursion-schemes`, `syntax-tree` allows parameterizing the "fix-point" of a syntax tree. Parameterized fix-points enabled useful combinators, conviniently "folding" the tree, annotating trees, pruning them, and more.

While `recursion-schemes` works best for ASTs with a single expression types, many ASTs are more complex and have several node types, for statements, expressions, types, etc. `syntax-tree` can represent these ASTs a single fix-point type parameter.

Not only are complex ASTs supported, the fix-points themselves may be equally rich. This allows for fix-points representing code diffs, and more.

## Heterogeneous AST examples

### Types and row types

Simple declaration of the AST without external fix-points:

```Haskell
data Typ
    = TInt
    | TFun Typ Typ
    | TRow Row

data Row
    = REmpty
    | RExtend String Typ Row
```

Note how `Typ`s has children of types `Typ` and `Row` (and `Row` also has children of both types). This makes it heterogeneous.

Here's how such a tree can be represented with `syntax-tree` with parameterized fix-points:

```Haskell
data Typ k
    = TInt
    | TFun (Node k Typ) (Node k Typ)
    | TRow (Row k)

data Row k
    = REmpty
    | RExtend String (Node k Typ) (Node k Row)
```

Differences:

* The child nodes are parameterized by a type variable "k"
* Nodes are specified via the `Node` type-synonym which "ties the knot"

## What kind of processing does `syntax-tree` do for me

* Helpers for recursive processing and transformation of ASTs
* Provides existing structures for common terms and fix-points
* A generic implementation for unification of terms
* A generic and fast implementation of a Hindley-Milner type inference algorithm (["Efficient generalization with levels"](http://okmij.org/ftp/ML/generalization.html#levels))

## The underlying principle: `Knot`s

* We want ASTs to be parameterized by fix-points
* We want fix-points to be parameterized by ASTs, too
* Therefore, ASTs and fix-points need to be mutually parameterized by each other
* This results in infinite types, as the AST is parameterized by something which may be parameterized by the AST itself.

To represent these infinite types we break the cycle with a `newtype`:

```Haskell
newtype Knot = Knot (Knot -> Type)
```

This allows representing the mutual parameterization:

* ASTs and fix-points are types parameterized by `Knot`s
* Their kind is therefore `Knot -> Type`
* `Knot -> Type` is also the kind of the type inside `Knot`, which is lifted to the type-level using `DataKinds`
* Wrapping the AST and fix-point type parameters with `Knot`s thus enables the mutual parameterization / recursion

### Relation to "Hyperfunctions"

S. Krstic et al [KLP2001] have described the a type which they call a "Hyperfunction". Here is it's definition from the [`hyperfunctions`](http://hackage.haskell.org/package/hyperfunctions) package on Hackage:

```Haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

`Knot`s are isomorphic to `Hyper Type Type` (assuming a `PolyKinds` variant of `Hyper`), so they can be seen as type-level "hyperfunctions".

For more info on hyperfunctions and their use cases in the value level see [LKS2013]

#### References

* [KLP2001] S. Krstic, J. Launchbury, and D. Pavlovic. Hyperfunctions. In Proceeding of Fixed Points in Computer Science, FICS 2001
* [LKS2013] J. Launchbury, S. Krstic, T. E. Sauerwein. [Coroutining Folds with Hyperfunctions](https://arxiv.org/abs/1309.5135). In In Proceedings Festschrift for Dave Schmidt, EPTCS 2013
* [`hyperfunctions`](http://hackage.haskell.org/package/hyperfunctions) package. E. A. Kmett. Hackage 2015
