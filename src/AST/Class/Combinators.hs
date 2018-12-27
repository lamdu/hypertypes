{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}

-- TODO: Document and find good names!

module AST.Class.Combinators
    ( And
    ) where

import AST.Knot (Knot)

-- Join two classes for usage with `children`/`ChildrenConstraint` or `Recursive`.
class (c0 k, c1 k) => And c0 c1 (k :: Knot -> *)
instance (c0 k, c1 k) => And c0 c1 k
