# syntax-tree: Higher-Kinded Data + recursion-schemes

Parameterizing data types by a "field constructor" is a widely used technique,
used by
the ["Higher-Kinded Data"](https://reasonablypolymorphic.com/blog/higher-kinded-data/) pattern and
by [`recursion-schemes`](http://hackage.haskell.org/package/recursion-schemes),
but these two approaches do not work well together and each one of them has its limitations.

* HKD parameterizes records on a functor to hold their fields.
  This pattern supports simple records but doesn't support nested structures.
* `recursion-schemes` parameterizes recursive structures by a fix-point.
  It doesn't support structures with several different types.
* A third approach, [`multirec`](http://hackage.haskell.org/package/multirec),
  does allow encoding nested and mutually recursive types with fix-points,
  by encoding each family of nested types as a single GADT.
  But using a single type imposes limitations on composabilty and modularity.

`syntax-tree` is a Haskell library for describing rich nested and mutually recursive types with
the "field constructor" parameter pattern, in a modular and composable manner.

## Introduction to the "field constructor" pattern and the status-quo

### `Type`: Simple type, simple functionality

Suppose we have the following type in an application:

```Haskell
data Person = Person
    { height :: Double
    , weight :: Double
    }
```

Let's imagine that we want to let a user fill in a `Person` via a form,
where during the process the record may have missing fields.

We may want a way to represent a state with missing fields,
but this type doesn't allow for it.

We can either create an additional type for that, or augment `Person` to provide more functionality. Augmenting `Person` is preferred because it will result in less boiler-plate and less types to maintain as we make changes to it.

### `Type -> Type`: Adding a type parameter

A possible solution is to parameterize `Person` on the field type:

```Haskell
data Person a = Person
    { height :: a
    , weight :: a
    }
```

This would solve our problem.

We can parameterize with `Double` for the normal structure,
and with `Maybe Double` for the variant with missing fields!

This approach reaches its limits when the fields have multiple different types, as in:

```Haskell
data Person = Person
    { height :: Double
    , weight :: Double
    , name :: Text
    }
```

We would now need an additional parameter to parameterize how to store the fields of type `Text`!
Is there a way to use a single type parameter for both types of fields? Yes, there is:

### `(Type -> Type) -> Type`: Higher-Kinded Data

We could represent `Person` like so:

```Haskell
data Person f = Person
    { height :: f Double
    , weight :: f Double
    , name :: f Text
    }
```

For the plain case we would use `Person Identity`.
`Identity` from `Data.Functor.Identity` is defined as so:

```Haskell
data Identity a = Identity a
```

And for the variant with missing fields we would use `Person Maybe`.

The benefit of this parameterization over the previous one is that `Person`'s kind
doesn't need to change when adding more field types, so such changes don't propagate all over the code base.

Note that various helper classes such as
`Rank2.Functor`
and `Rank2.Traversable` (from the [`rank2classes`](https://hackage.haskell.org/package/rank2classes) package)
allow us to conviniently convert between `Person Identity` and `Person Maybe`.

#### HKD for nested structures

Let's employ the same transformation we did for `Person` to a more complicated data structure:

```Haskell
data Expr
    = Const Int
    | Add Expr Expr
    | Mul Expr Expr
```

The HKD form of `Expr` would be:

```Haskell
data Expr f
    = Const (f Int)
    | Add (f (Expr f)) (f (Expr f))
    | Mul (f (Expr f)) (f (Expr f))
```

This does allow representing nested structures with missing elements.
But classes like `Rank2.Functor` no longer work for it.
To understand why let's look at `Rank2.Functor`'s definition

```Haskell
class Functor f where
    (<$>) :: (forall a. p a -> q a) -> f p -> f q
```

The rank-2 function argument expects the field type `a` to stay the same when it changes `p` to `q`,
however in the above formulation of `Expr` the field type `Expr p` change to `Expr q` when changing the type parameter.

### `Type -> Type`: The `recursion-schemes` approach

The `recursion-schemes` formulation of `Expr` is the same as the `Type -> Type` approach discussed above:

```Haskell
data Expr a
    = Const Int
    | Add a a
    | Mul a a
```

(Note that `recursion-schemes` can generate it for us from the simple definition of `Expr` using `TemplateHaskell`)

This approach does have the single node type limitation, so we gave up on parameterizing over the `Int` in `Const`.
This is a big limitation, but we do get several advantages.

We can represent an expression as `Fix Expr`, using:

```Haskell
newtype Fix f = Fix (f (Fix f))
```

We can then use useful combinators from `recursion-schemes` for folding and processing of `Expr`s.

[`unification-fd`](http://hackage.haskell.org/package/unification-fd)
is a good example for the power of this approach.
It implements unification for ASTs,
where it uses the parameterization to store unification variables standing for terms.

In constrast to the HKD approach, we can also use rich fix-points which store several different fix-points within, like `Diff`:

```Haskell
data Diff f
    = Same (f (Fix f))
    | SameTopLevel (f (Diff f))
    | Different (f (Fix f)) (f (Fix f))
```

(Note how `Diff` parameterizes `f` by both `Fix` and `Diff`)

The main drawback of this approach is that in practice ASTs tend to be mutually recursive datatypes. For example:

```Haskell
data Expr
    = Var Text
    | App Expr Expr
    | Lam Text Typ Expr
data Typ
    = IntT
    | FuncT Typ Typ
```

This type is an example for an AST which `recursion-schemes` can't help us with.

Is there a way to present this structure? Yes:

### `(Index -> Type) -> Index -> Type`: The `multirec` approach

[`multirec`](http://hackage.haskell.org/package/multirec)'s way to define the above AST:

```Haskell
data Expr :: Index
data Typ :: Index

data AST :: (Index -> Type) -> Index -> Type where
    Var :: Text -> AST r Expr
    App :: r Expr -> r Expr -> AST r Expr
    Lam :: Text -> r Typ -> r Expr -> AST r Expr
    IntT :: AST r Typ
    FuncT :: r Typ -> r Typ -> AST r Typ
```

(this is a slight variant of `multirec`'s actual presentation, where for improved legibility `Index` is used rather than `Type`)

`multirec` offers various utilities to process such data types.
It offers [`HFunctor`](http://hackage.haskell.org/package/multirec-0.7.9/docs/Generics-MultiRec-HFunctor.html),
a variant of `Functor` for these structures, and various recursive combinators.

But `multirec` has several limitations:

* Using a single GADT for the data type limits composition and modularity.
* Invocations of `HFunctor` for a `Typ` node need to support transforming all indices of `AST`,
  including `Expr`, even though `Typ` doesn't have `Expr` child nodes.

## `Knot -> Type`: `syntax-tree`'s approach

The `syntax-tree` representation of the above AST example:

```Haskell
data Expr k
    = Var Text
    | App (k # Expr) (k # Expr)
    | Lam Text (k # Typ) (k # Expr)
data Typ k
    = IntT
    | FuncT (k # Typ) (k # Typ)
```

The `#` type operator used above requires introduction:

```Haskell
type k # p = (GetKnot k) ('Knot p)

newtype Knot = Knot (Knot -> Type)

-- GetKnot is a getter from the Knot newtype lifted to the type level
type family GetKnot k where
    GetKnot ('Knot t) = t
```

(`'Knot` is `DataKinds` syntax for using the `Knot` data constructor in types)

For this representation, `syntax-tree` offers the power and functionality of HKD, `recursion-schemes`, `multirec`, and some useful helpers:

* Variants of standard classes like `Functor` with `TemplateHaskell` derivations for them.
  (Unlike in `multirec`'s `HFunctor`, only the actual child node types of each node need to be handled)
* Combinators for recursive processing and transformation of nested structures
* Implementations for common AST terms and useful fix-points
* A `unification-fd` inspired unification implementation for mutually recursive types
* A generic and fast implementation of a Hindley-Milner type inference algorithm (["Efficient generalization with levels"](http://okmij.org/ftp/ML/generalization.html#levels))

## Usage examples



## Understanding `Knot`s

* We want structures to be parameterized by fix-points
* Fix-points are parameterized by the structures, too
* Therefore, structures and their fix-points need to be parameterized by each other
* This results in infinite types, as the structure is parameterized by something which may be parameterized by the structure itself.

`multirec` ties this knot by using indices to represent types. `syntax-tree` does this by using `DataKinds` and the `Knot` `newtype` which is used for both structures and their fix-points An implication of the two being the same is that the same classes and combinators are re-used for both.

## How does syntax-tree compare/relate to

Note that comparisons to HKD, `recursion-schemes`, `multirec`, `rank2classes`, and `unification-fd` were discussed in depth above.

In addition:

### hyperfunctions

S. Krstic et al [KLP2001] have described the a type which they call a "Hyperfunction". Here is it's definition from the [`hyperfunctions`](http://hackage.haskell.org/package/hyperfunctions) package:

```Haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

`Knot`s are isomorphic to `Hyper Type Type` (assuming a `PolyKinds` variant of `Hyper`), so they can be seen as type-level "hyperfunctions".

For more info on hyperfunctions and their use cases in the value level see [LKS2013]

#### References

* [KLP2001] S. Krstic, J. Launchbury, and D. Pavlovic. Hyperfunctions. In Proceeding of Fixed Points in Computer Science, FICS 2001
* [LKS2013] J. Launchbury, S. Krstic, T. E. Sauerwein. [Coroutining Folds with Hyperfunctions](https://arxiv.org/abs/1309.5135). In In Proceedings Festschrift for Dave Schmidt, EPTCS 2013

### bound

[`bound`](http://hackage.haskell.org/package/bound) is a library for expressing ASTs with type-safe De-Bruijn indices rather than parameter names, via an AST type constructor that is indexed on the variables in scope.

An intereseting aspect of `bound`'s ASTs is that recursively they are made of an infinite amount of types.

When implementing `syntax-tree` we had the explicit goal of making sure that such ASTs are expressible with it,
and for this reason the `AST.Term.NamelessScope` module implementing it is provided, and the test suite includes
a language implementation based on it (`LangA` in the tests).

### lens

`syntax-tree` strives to be maximally compatible with [`lens`](http://hackage.haskell.org/package/lens), and offers `Traversal`s and `Setter`s wherever possible. But unfortunately the `RankNTypes` nature of many combinators in syntax-tree makes them not composable with optics. For the special simpler cases when all child nodes have the same types the `traverseK1` traversal and `mappedK1` setter are available.
