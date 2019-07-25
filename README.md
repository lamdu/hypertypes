# syntax-tree

**Note:** Currently the library is in the process of shifting from the `Children` class to classes like `KTraversable`. Documentation and example may currently reflect to-be-obsoleted practices.

A Haskell library for representing syntax trees using type-level interleaved continuations, and processing these trees.

Like [`recursion-schemes`](https://github.com/ekmett/recursion-schemes/),
`syntax-tree` allows parameterizing the "fix-point" of a syntax tree. Parameterized fix-points allow various useful things, like adding annotations on all nodes, conviniently "folding" the tree, pruning trees, and more.

But unlike `recursion-schemes`, heterogeneous ASTs represented using `syntax-tree` can share a single fix-point type,
meaning that there could be "statement" nodes containing "expression" nodes, etc. all sharing the same fix-point.

The fix-points for ASTs may also be heterogeneous, allowing for fix-points representing code diffs, and more.

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

* The types are parameterized by a type variable "k"
* Node children are specified via the `Node` type-synonym which "ties the knot"

## What does `syntax-tree` do for me

* Allow representing ASTs in a type-safe and versatile manner
* Helpers for recursive processing and transformation of ASTs
* Provides existing structures for common terms and fix-points
* A generic implementation for unification of terms
* A generic and fast implementation of a Hindley-Milner type inference algorithm (["Efficient generalization with levels"](http://okmij.org/ftp/ML/generalization.html#levels))

## The underlying principle: `Knot`s

* We want ASTs to be parameterized by fix-points
* We want fix-points to be parameterized by ASTs, too
* Therefore, ASTs and fix-points need to be mutually parameterized by each other
* The AST parameterized by a fix-point which may be parameterized by the same AST results in infinite types

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
