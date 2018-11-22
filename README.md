# syntax-tree

A Haskell library for diverse (non-uniform) typed syntax trees with external fix-points, for example:

```Haskell
data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)
```

What makes the above tree diverse is that `RExtend` must contain one `Typ` and one `Row`.

Many libraries for syntax trees using external fix-points assume that all the tree nodes are of the same type.
