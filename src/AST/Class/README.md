# AST Classes

Classes for AST types:

* `Children expr` => `expr` has immediate sub-nodes.
* `Recursive cls expr` => All of `expr`s recursive sub-nodes support `cls`.
* `ZipMatch` compares structures.
* `TH` generates instances for the classes using Template Haskell.