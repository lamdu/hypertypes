# syntax-tree: Higher-Kinded Data all the way down!

syntax-tree is a Haskell library for working with higher kinded data structures.

It allows to describe nested data structures parameterised on how to store child nodes.

## Comparison to simple HKD

[Higher-Kinded Data](http://reasonablypolymorphic.com/blog/higher-kinded-data) (aka HKD) enables parameterizing items in a record, allowing for example to represent a variant of the record which may have missing items.

With HKD-all-the-way-down (aka nested-HKD), instead of containing simple values of kind `Type`, the structure contains similar nested-HKD structures.

## Examples

### Heterogeneous AST of types and row types

Let's consider the following AST:

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

Here's how such a tree can be represented as nested-HKD with `syntax-tree`:

```Haskell
data Typ k
    = TInt
    | TFun (Node k Typ) (Node k Typ)
    | TRow (Row k)

data Row k
    = REmpty
    | RExtend String (Node k Typ) (Node k Row)
```

Differences from the simple type definition:

* The types are parameterized by `k`
* Nodes are specified via the `Node` type-synonym which "ties the knot", with `k` and the node type

## What can syntax-tree do for you

* Nested-HKD variants of standard classes like `Functor`
* Helpers for recursive processing and transformation of nested structures
* A generic implementation for unification of terms
* A generic and fast implementation of a Hindley-Milner type inference algorithm (["Efficient generalization with levels"](http://okmij.org/ftp/ML/generalization.html#levels))
* Implementations for common AST terms and useful fix-points


## The underlying principle: `Knot`s

* We want ASTs to be parameterized by fix-points
* Fix-points are parameterized by the ASTs, too
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

## How does syntax-tree compare to

### recursion-schemes

[recursion-schemes](http://hackage.haskell.org/package/recursion-schemes) offers combinators for processing homogeneous recursive types.

The heterogeneous AST example above is an example for non-homogeneous, co-recursive types. syntax-tree offers combinators which are similar to those from recursion-schemes but which also work for heterogeneous structures.

### rank2classes

[rank2classes](https://hackage.haskell.org/package/rank2classes) offers rank-2 variants of common classes such as `Functor`:

```Haskell
class Rank2.Functor g where
    (<$>) ::
        (forall a. p a -> q a) ->
        g p ->
        g q
```

This is very similar to syntax-tree's `KFunctor`:

```Haskell
class KNodes g => KFunctor g where
    mapK ::
        (forall a. p a -> q a) ->
        g ('Knot p) ->
        g ('Knot q)
    mapKWith :: ...
```

`mapK` and `Rank2.(<$>)` are similar, but an important difference is that `g`'s parameters `p` and `q` are wrapped in `Knot`, because this is how syntax-tree's nested-HKD work. That is, knots can't be instances of `Rank2.Functor` and this is why the `KFunctor` variant is necessary.

 Additionally, `mapKWith` is provided, which allows using a mapping that requires a constraint on the child nodes, which is an extensively used feature.

### unification-fd

[unification-fd](http://hackage.haskell.org/package/unification-fd) provides a unification implementation for homogeneous recursive types.

syntax-tree provides a unification implementation for heterogeneous ASTs. Furthermore, syntax-tree also provides an implementation for Hindley-Milner type inference, with the `Infer` type class and with implementations of common AST terms which one can re-use as components in their own AST types.

### hyperfunctions

S. Krstic et al [KLP2001] have described the a type which they call a "Hyperfunction". Here is it's definition from the [hyperfunctions](http://hackage.haskell.org/package/hyperfunctions) package:

```Haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

`Knot`s are isomorphic to `Hyper Type Type` (assuming a `PolyKinds` variant of `Hyper`), so they can be seen as type-level "hyperfunctions".

For more info on hyperfunctions and their use cases in the value level see [LKS2013]

#### References

* [KLP2001] S. Krstic, J. Launchbury, and D. Pavlovic. Hyperfunctions. In Proceeding of Fixed Points in Computer Science, FICS 2001
* [LKS2013] J. Launchbury, S. Krstic, T. E. Sauerwein. [Coroutining Folds with Hyperfunctions](https://arxiv.org/abs/1309.5135). In In Proceedings Festschrift for Dave Schmidt, EPTCS 2013
