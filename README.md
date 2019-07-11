# syntax-tree

A Haskell library for representing and processing syntax trees.

Like [`recursion-schemes`](https://github.com/ekmett/recursion-schemes/),
`syntax-tree` allows parameterizing the "fix-point" of the tree. Parameterized fix-points allow various useful things, like adding annotations on all nodes, conviniently "folding" the tree, pruning trees, and more.

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
    | TFun (Tie k Typ) (Tie k Typ)
    | TRow (Row k)

data Row k
    = REmpty
    | RExtend String (Tie k Typ) (Tie k Row)
```

Differences:

* The types are parameterized by a type variable "k"
* Node children are specified via the `Tie` type-synonym which "ties the knot"

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
