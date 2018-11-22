# syntax-tree

A Haskell library for diverse (non-uniform) typed syntax trees with external fix-points.

Let's consider this recursive diverse AST (without external fix-point):

```Haskell
data Typ
    = TInt
    | TFun Typ Typ
    | TRow Row

data Row
    = REmpty
    | RExtend String Typ Row
```

Note how `RExtend` contains both a `Typ` and a `Row`. This makes this a non-uniform tree.

Many libraries and tutorials for representing ASTs in Haskell with external fix-points,
suggest to formulate the tree with a type variable for its children,
however when the tree is diverse that solution doesn't work.

Here's how this library provides an external fix-point to the above AST:

```Haskell
data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)
```