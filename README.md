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
    | TFun (k ('Knot Typ)) (k ('Knot Typ))
    | TRow (Row k)

data Row k
    = REmpty
    | RExtend String (k ('Knot Typ)) (k ('Knot Row))
```

Differences from the simple type definition:

* The types are parameterized by `k`
* Child nodes are constructed by applying `k` with the node type (wrapped by `'Knot`)

## What can syntax-tree do for you

* Helpers for recursive processing and transformation of nested structures
* Nested-HKD variants of standard classes like `Functor`
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

## How does syntax-tree compare/relate to

### recursion-schemes

[recursion-schemes](http://hackage.haskell.org/package/recursion-schemes) offers combinators for processing homogeneous recursive types.

The heterogeneous AST example above is an example for non-homogeneous, co-recursive types. syntax-tree offers combinators which are similar to those from recursion-schemes but which also work for heterogeneous structures.

### rank2classes

[rank2classes](https://hackage.haskell.org/package/rank2classes) offers rank-2 variants of common classes such as `Functor`:

```Haskell
class Rank2.Functor f where
    (<$>) ::
        (forall a. p a -> q a) ->
        f p ->
        f q
```

This is very similar to syntax-tree's `KFunctor`:

```Haskell
class KNodes f => KFunctor f where
    mapK ::
        (forall a. p a -> q a) ->
        f ('Knot p) ->
        f ('Knot q)
    mapKWith :: ...
```

`mapK` and `Rank2.(<$>)` are similar, but an important difference is that `g`'s parameters `p` and `q` are wrapped in `Knot`, because this is how syntax-tree's nested-HKD work. That is, knots can't be instances of `Rank2.Functor` and this is why the `KFunctor` variant is necessary.

 Additionally, `mapKWith` is provided, which allows using a mapping that requires a constraint on the child nodes, which is an extensively used feature.

### compdata

[compdata](http://hackage.haskell.org/package/compdata) also offers a method to describe heterogenous structures with external fixpoints and also offers variants of common classes such as `Functor`:

```Haskell
class HFunctor f where
    hfmap ::
        (forall a. p a -> q a) ->
        f p b ->
        f q b
```

Differences between compdata and syntax-tree:

* compdata requires the nested structures to be described together in a single indexed data type (via `GADT`s or data familes). syntax-tree also allows structures to be split across separate data types, which allows for more modularity and code reusability
* syntax-tree's `KFunctor` also provides `mapKWith` which allows mappings to use constraints on child nodes, which is used extensively

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

### bound

[bound](http://hackage.haskell.org/package/bound) is a library for expressing ASTs with type-safe De-Bruijn indices rather than parameter names, via an AST type constructor that is indexed on the variables in scope.

An intereseting aspect of bound's ASTs is that recursively they are made of an infinite ammount of types.

When implementing syntax-tree we had the explicit goal of making sure that such ASTs are expressible with it,
and for this reason the `AST.Term.NamelessScope` module implementing it is provided, and the test suite includes
a language implementation based on it (`LangA` in the tests).

### lens

syntax-tree strives to be maximally compatible with [lens](http://hackage.haskell.org/package/lens), and offers `Traversal`s and `Setter`s wherever possible. But unfortunately the `RankNTypes` nature of many combinators in syntax-tree makes them not composable with optics. For the special simpler cases when all child nodes have the same types the `traverseK1` traversal and `mappedK1` setter are available.
