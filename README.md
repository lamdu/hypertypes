# syntax-tree

A Haskell library for representing and processing syntax trees.

Like [`recursion-schemes`](https://github.com/ekmett/recursion-schemes/),
`syntax-tree` allows parameterizing the "fix-point" of the tree. Parameterized fix-points allow various useful things, like adding annotations on all nodes, conviniently "folding" the tree, pruning trees, and more.

But unlike `recursion-schemes`, ASTs represented using `syntax-tree` can be heterogeneous,
meaning that there could be "statement" nodes containing "expression" nodes etc.

Not only that, the fix-points may also be heterogeneous,
allowing for fix-points representing code diffs, and more.

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
* We also want fix-points to be parameterized by ASTs (to specify the AST types of child nodes)
* Therefore, ASTs should be parameterized by something which is parameterized by them! This results in infinite types!

To work around the infinite types we break the cycle with a `newtype`:

```Haskell
newtype Knot = Knot (Knot -> Type)
```

Instead of being parameterized by fix-points directly, ASTs are parameterized by them wrapped with `Knot`

How does it work:

* ASTs (and their fix-points too) are types parameterized by `Knot`s
* Their kind is therefore `Knot -> Type`
* `Knot -> Type` is also the kind of the value inside `Knot`
* The type constructors of ASTs and of fix-points can be thus wrapped with `'Knot` (the `Knot` data constructor lifted to types with `DataKinds`)
