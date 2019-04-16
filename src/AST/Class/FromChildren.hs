{-# LANGUAGE NoImplicitPrelude, RankNTypes, ConstraintKinds #-}

module AST.Class.FromChildren
    ( FromChildren(..)
    ) where

import AST (Tree, ChildrenConstraint, Pure, _Pure)
import AST.Knot.Functor (ToKnot(..))
import Control.Lens.Operators
import Data.Proxy (Proxy)

import Prelude.Compat

class FromChildren parent where
    fromChildren ::
        (Applicative f, ChildrenConstraint parent constraint) =>
        Proxy constraint ->
        (forall child. constraint child => f (Tree k child)) ->
        f (Tree parent k)

instance FromChildren Pure where
    fromChildren _ mk = mk <&> (_Pure #)

instance Applicative f => FromChildren (ToKnot f) where
    fromChildren _ mk = mk <&> pure <&> ToKnot
