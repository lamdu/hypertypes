# AST Classes

Classes for AST types:

* `Children` types have sub-nodes.
* `Recursive` classes are those that apply recursively to sub-nodes, `ChildrenRecursive` means that `Children` is available for all sub-nodes.
* `ZipMatch` compares structures.
* `TH` generates instances for the classes using Template Haskell.