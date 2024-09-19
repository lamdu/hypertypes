# hypertypes: Types parameterised by hypertypes

Hypertypes enable constructing rich recursive types from individual components, and processing them generically with type classes.

They are a solution to the *Expression Problem*, as described by Phil Wadler (1998):

> The goal is to define a data type by cases, where one can add new cases to the data type and new functions over the data type, without recompiling existing code, and while retaining static type safety.

[*Data types a la carte*](http://www.staff.science.uu.nl/~swier004/publications/2008-jfp.pdf) (DTALC, Swierstra, 2008) offers a solution for the expression problem which is only applicable for simple recursive expressions, without support for mutually recursive types. In practice, programming language ASTs do tend to be mutually recursive. [`multirec`](http://hackage.haskell.org/package/multirec) (Rodriguez et al, 2009) uses GADTs to encode mutually recursive types but in comparison to DTALC it lacks in the ability to construct the types from re-usable components.

Hypertypes allow constructing expressions from re-usable terms like DTALC, which can be rich mutually recursive types like in `multirec`.

The name "Hypertypes" is inspired by *Hyperfunctions* (S. Krstic et al, FICS 2001), which are a similar construct at the value level.

## Introduction to the "field constructor" pattern

To motivate hypertypes and explain the expressive power they allow, this section will discuss the benefits and limitations of other forms of constructing data types, ranging from unparameterized types to more powerful approaches:

* `Type` - unparameterized types
* `Type -> Type` - simple parameterized types
* `(Type -> Type) -> Type` - also known as HKD (Higher-Kinded Data)
* `(Index -> Type) -> Index -> Type` - `multirec`'s approach

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
and with `Maybe Double` for the variant with missing fields.

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

The ["Higher-Kinded Data"](https://reasonablypolymorphic.com/blog/higher-kinded-data/) pattern represents `Person` like so:

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
allow us to conveniently convert between `Person Identity` and `Person Maybe`.

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

### `Type -> Type`: The DTALC and `recursion-schemes` approach

Another formulation of `Expr` is the same as the `Type -> Type` approach discussed above:

```Haskell
data Expr a
    = Const Int
    | Add a a
    | Mul a a
```

Notes:

* The [`recursion-schemes`](http://hackage.haskell.org/package/recursion-schemes) package can generate this type for us from the plain definition of `Expr` using `TemplateHaskell`
* DTALC also allows us to construct this type by combining standalone `Const`, `Add`, and `Mul` types with the `:+:` operator (i.e `Const Int :+: Add :+: Mul`)

This approach does have the single node type limitation, so we gave up on parameterizing over the `Int` in `Const`.
This is a big limitation, but as we'll see, we do get several advantages in return.

First, we can represent plain expressions as `Fix Expr`, using:

```Haskell
newtype Fix f = Fix (f (Fix f))
```

We can then use useful combinators from `recursion-schemes` for folding and processing of `Expr`s.

[`unification-fd`](http://hackage.haskell.org/package/unification-fd)
is a good example of the power of this approach.
It implements generic unification for ASTs,
where it uses the parameterization to represent sub-expressions via unification variables.

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

This type is an example for an AST which DTALC and `recursion-schemes` cannot represent.

Can the "field constructor" pattern be used to represent such ASTs? Yes:

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

## `hypertypes`'s approach

The `hypertypes` representation of the above AST example:

```Haskell
data Expr h
    = EVar Text
    | EApp (h :# Expr) (h :# Expr)
    | ELam Text (h :# Typ) (h :# Expr)
data Typ h
    = TInt
    | TFunc (h :# Typ) (h :# Typ)
```

Sub-expressions are nested using the `:#` type operator. On the left side of `:#` is `Expr`'s type parameter `h` which is the "nest type", and on the right side `Expr` and `Typ` are the nested nodes.

`:#` is defined as:

```Haskell
-- A type parameterized by a hypertype
type HyperType = AHyperType -> Type

-- A kind for hypertypes
newtype AHyperType = AHyperType { getHyperType :: HyperType }

-- GetHyperType is getHyperType lifted to the type level
type family GetHyperType h where
    GetHyperType ('AHyperType t) = t

type p :# q = (GetHyperType p) ('AHyperType q)
-- AHyperType is DataKinds syntax for using AHyperType in types
```

The `hypertypes` library provides:

* Variants of standard classes like `Functor` for hypertypes with derivations.
  (Unlike in `multirec`'s `HFunctor`, only the actual child node types of each node need to be handled)
* Combinators for recursive processing and transformation of nested structures
* Implementations of common AST terms
* A unification implementation for mutually recursive types inspired by `unification-fd`
* A generic and fast implementation of Hindley-Milner type inference ("Efficient generalization with levels" as described in [*How OCaml type checker works*](http://okmij.org/ftp/ML/generalization.html), Kiselyov, 2013)

## Constructing types from individual components

Note that another way to formulate the above expression would be using pre-existing parts, such as:

```Haskell
data RExpr h
    = RVar (Var Text RExpr h)
    | RApp (App RExpr h)
    | RLam (TypedLam Text Typ RExpr h)
    deriving (Generic, Generic1, HNodes, HFunctor, HFoldable, HTraversable, ZipMatch)
```

This form supports using `DeriveAnyClass` to derive instances for various `HyperType` classes such as `HFunctor` based on `Generic1`. Note that due to a technical limitation of `Generic1` the form of `Expr` from before, which directly nests values, doesn't have a `Generic1` instance (so the instances for `Expr` are derived using `TemplateHaskell` instead).

## Examples

How do we represent an expression of the example language declared above?

Let's start with the verbose way:

```Haskell
verboseExpr :: Pure # Expr
verboseExpr =
    Pure (ELam "x" (Pure TInt) (Pure (EVar "x")))
```

Explanations for the above:

* `Pure # Expr` is a type synonym for `Pure ('AHyperType Expr)`
* `Pure` is the simplest "pass-through" nest type
* The above is quite verbose with a lot of instances of `Pure` and many parentheses
* Writing an expression of the above `RExpr` would be even more verbose due to additional `Var` and `TypedLam` data constructors!

To write it more consicely, the `HasHPlain` class, along with a `TemplateHaskell` generator for it, exists:

```Haskell
> let e = hPlain # verboseExpr
-- Note: This (#) comes from Control.Lens

> e
ELamP "x" TIntP (EVarP "x")

> :t e
e :: HPlain Expr
```

It's now easier to see that `e` represents `λ(x:Int). x`

`HPlain` is a data family of "plain versions" of expressions, generated via `TemplateHaskell`. Note that it flattens embedded constructors for maximal convinience, so that the plain version of `RExpr` is as convinient to use as that of `Expr`!

This is somewhat similar to how `recursion-schemes` can derive a parameterized version of an AST, but is the other way around: the parameterized type is the source and the plain one is generated.

So now, let's define some example expressions concisely:

```Haskell
exprA, exprB :: HPlain Expr

exprA = ELamP "x" IntTP (EVarP "x")

exprB = ELamP "x" (TFuncP TIntP TIntP) (EVarP "x")
```

What can we do with these expressions?
Let's compute a diff:

```Haskell
> let d = diffP exprA exprB

> d
CommonBodyP
(ELam "x"
    (DifferentP TIntP (TFuncP TIntP TIntP))
    (CommonSubTreeP (EVarP "x"))
)

> :t d
d :: DiffP # Expr
-- (An Expr with the DiffP nest type)
```

Let's see the type of `diffP`:

```Haskell
> :t diffP
diffP ::
    ( RTraversable h
    , Recursively ZipMatch h
    , Recursively HasHPlain h
    ) =>
    HPlain h -> HPlain h -> DiffP # h
```

`diffP` can compute the diff for any AST that is recursively traversable, can be matched, and has a plain representation.

Now, let's format this diff better:

```Haskell
> let formatDiff _ x y = "- " <> show x <> "\n+ " <> show y <> "\n"

> putStrLn (foldDiffsP formatDiff d)
- TIntP
+ TFuncP TIntP TIntP

> :t foldDiffsP
foldDiffsP ::
    ( Monoid r
    , Recursively HFoldable h
    , Recursively HasHPlain h
    ) =>
    (forall n. HasHPlain n => HRecWitness h n -> HPlain n -> HPlain n -> r) ->
    DiffP # h ->
    r
```

Why is the ignored argument of `formatDiff` there? It is the `HRecWitness h n` from the type of `foldDiffsP` above. It is a witness that "proves" that the folded node `n` is a recursive node of `h`, essentially restricting the `forall n.` to `n`s that are recursive nodes of `h`.

## Witness parameters

*First, I want to give thanks and credit: We learned of this elegant solution from `multirec`!*

What are witness parameters?

Let's look at how `HFunctor` is defined:

```Haskell
class HNodes h => HFunctor h where
    -- | 'HFunctor' variant of 'fmap'
    hmap ::
        (forall n. HWitness h n -> p # n -> q # n) ->
        h # p ->
        h # q
```

`HFunctor` can change an `h`'s nest-type from `p` to `q`.

`HWitness` is a data family which is a member of `HNodes`.

For example, let's see the definition of `Expr`'s `HWitness`:

```Haskell
data instance HWitness Expr n where
    W_Expr_Expr :: HWitness Expr Expr
    W_Expr_Typ :: HWitness Expr Typ
```

Note that this GADT is automatically generated via `TemplateHaskell`.

What does the witness give us? It restricts `forall n.` to the nodes of `h`.
When mapping over an `Expr` we can:

* Ignore the witness and use a mapping from a `p` of any `n` to a `q` of it
* Pattern match on the witness to handle `Expr`'s specific node types
* Use the `#>` operator to convert the witness to a class constraint on `n`.

## Understanding `HyperType`s

* We want structures to be parameterized by nest-types
* Nest-types are parameterized by the structures, too
* Therefore, structures and their nest-types need to be parameterized by each other
* This results in infinite types, as the structure is parameterized by something which may be parameterized by the structure itself.

`multirec` ties this knot by using indices to represent types. `hypertypes` does this by using `DataKinds` and the `AHyperType` `newtype` which is used for both structures and their nest-types. An implication of the two being the same is that the same classes and combinators are re-used for both.

## What Haskell is this

`hypertypes` is implemented with GHC and heavily relies on quite a few language extensions:

* `ConstraintKinds` and `TypeFamilies` are needed for the `HNodesConstraint` type family that lifts a constraint to apply over a value's nodes. Type families are also used to encode term's results in type inference.
* `DataKinds` allows parameterizing types over `AHyperType`s
* `DefaultSignatures` are used for default methods that return `Dict`s to avoid undecidable super-classes
* `DeriveGeneric`, `DerivingVia`, `GeneralizedNewtypeDeriving`, `StandaloneDeriving` and `TemplateHaskell` are used to derive type-class instances
* `EmptyCase` is needed for instances of leaf nodes
* `FlexibleContexts`, `FlexibleInstances` and `UndecidableInstances` are required to specify many constraints
* `GADTs` and `RankNTypes` enable functions like `hmap` which get `forall`ed functions with witness parameters
* `MultiParamTypeClasses` is needed for the `Unify` and `Infer` type classes
* `ScopedTypeVariables` and `TypeApplications` assist writing short code that type checks
* `PolyKinds` is required for the generated instances

Many harmless syntactic extensions are also used:

* `DerivingStrategies`, `LambdaCase`, `TupleSections`, `TypeOperators`

## How does hypertypes compare/relate to

Note that comparisons to `multirec`, HKD, `recursion-schemes`, `rank2classes`, and `unification-fd` were discussed above.

In addition:

### hyperfunctions

S. Krstic et al [KLP2001] have described the a type which they call a "Hyperfunction". Here is it's definition from the [`hyperfunctions`](http://hackage.haskell.org/package/hyperfunctions) package:

```Haskell
newtype Hyper a b = Hyper { invoke :: Hyper b a -> b }
```

`AHyperType`s are isomorphic to `Hyper Type Type` (assuming a `PolyKinds` variant of `Hyper`), so they can be seen as type-level "hyperfunctions".

For more info on hyperfunctions and their use cases in the value level see [LKS2013]

#### References

* [KLP2001] S. Krstic, J. Launchbury, and D. Pavlovic. Hyperfunctions. In Proceeding of Fixed Points in Computer Science, FICS 2001
* [LKS2013] J. Launchbury, S. Krstic, T. E. Sauerwein. [Coroutining Folds with Hyperfunctions](https://arxiv.org/abs/1309.5135). In In Proceedings Festschrift for Dave Schmidt, EPTCS 2013

### Data Types a la Carte

In addition to the external fix-points described above, [Data Types a la Carte](http://www.staff.science.uu.nl/~swier004/publications/2008-jfp.pdf) (DTALC) also describes how to define ASTs structurally.

I.e, rather than having

```Haskell
data Expr a
    = Val Int
    | Add a a -- "a" stands for a sub-expression (recursion-schemes style)
```

We can have

```Haskell
newtype Val a = Val Int

data Add a = Add a a

-- Expr is a structural sum of Val and Add
type Expr = Val :+: Add
```

This enables re-usability of the AST elements `Val` and `Add` in various ASTs, where the functionality is shared via type classes. Code using these type classes can work generically for different ASTs.

Like DTALC, `hypertypes` has:

* Instances type for combinators such as `:+:` and `:*:`, so that these can be used to build ASTs
* Implementations of common AST terms in the `Hyper.Type.AST` module hierarchy (`App`, `Lam`, `Let`, `Var`, `TypeSig` and others)
* Classes like `HFunctor`, `HTraversable`, `Unify`, `Infer` with instances for the provided AST terms

As an example of a reusable term let's look at the definition of `App`:

```Haskell
-- | A term for function applications.
data App expr h = App
    { _appFunc :: h :# expr
    , _appArg :: h :# expr
    }
```

Unlike a DTALC-based apply, which would be parameterized by a single type parameter `(a :: Type)`, `App` is parameterized on two type parameters, `(expr :: HyperType)` and `(h :: AHyperType)`. `expr` represents the node type of `App expr`'s child nodes and `h` is the tree's fix-point. This enables using `App` in mutually recursive ASTs where it may be parameterized by several different `expr`s.

Unlike DTALC, in `hypertypes` one typically needs to explicitly declare the datatypes for their expression types so that they can be used as `App`'s `expr` type parameter. Similarly, `multirec`'s DTALC variant also requires explicitly declaring type indices.

While it is possible to declare ASTs as `newtype`s wrapping `:+:`s of existing terms and deriving all the instances via `GeneralizedNewtypeDeriving`, our usage and examples declare types in the straight forward way, with named data constructors, as we think that this results in more readable and performant code.

### bound

[`bound`](http://hackage.haskell.org/package/bound) is a library for expressing ASTs with type-safe De-Bruijn indices rather than parameter names, via an AST type constructor that is indexed on the variables in scope.

An intereseting aspect of `bound`'s ASTs is that recursively they are made of an infinite amount of types.

When implementing `hypertypes` we had the explicit goal of making sure that such ASTs are expressible with it,
and for this reason the `Hyper.Type.AST.NamelessScope` module in the tests implementing it is provided, and the test suite includes
a language implementation based on it (`LangA` in the tests).

### lens

`hypertypes` strives to be maximally compatible with [`lens`](http://hackage.haskell.org/package/lens), and offers `Traversal`s and `Setter`s wherever possible. But unfortunately the `RankNTypes` nature of many combinators in hypertypes makes them not composable with optics. For the special simpler cases when all child nodes have the same types the `htraverse1` traversal and `hmapped1` setter are available.
