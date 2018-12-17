# syntax-tree

A Haskell library for diverse (non-uniform) typed syntax trees with external fix-points ("Knots").

Let's consider this co-recursive AST (without knots):

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
however when the tree is diverse that solution doesn't work (because the children are not of the same type).

Here's how this library represents the above AST with Knots:

```Haskell
data Typ k
    = TInt
    | TFun (Tie k Typ) (Tie k Typ)
    | TRow (Row k)

data Row k
    = REmpty
    | RExtend String (Tie k Typ) (Tie k Row)
```
