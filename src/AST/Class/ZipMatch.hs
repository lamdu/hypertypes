{-# LANGUAGE NoImplicitPrelude, RankNTypes, ConstraintKinds, ScopedTypeVariables #-}

module AST.Class.ZipMatch
    ( ZipMatch(..)
    , zipMatch_
    ) where

import           AST.Class.Children (Children(..))
import           AST.Node (Node)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy)

import           Prelude.Compat

class Children expr => ZipMatch expr where
    zipMatch ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node a child -> Node b child -> f (Node c child)) ->
        expr a -> expr b -> Maybe (f (expr c))

zipMatch_ ::
    forall f expr constraint a b.
    (Applicative f, ZipMatch expr, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Node a child -> Node b child -> f ()) ->
    expr a -> expr b -> Maybe (f ())
zipMatch_ p f x y =
    ( zipMatch p (f <&> Lens.mapped . Lens.mapped .~ Const ()) x y
        :: Maybe (f (expr (Const ())))
    ) <&> Lens.mapped .~ ()
