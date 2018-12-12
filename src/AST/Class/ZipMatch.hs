{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoImplicitPrelude, RankNTypes, ConstraintKinds, ScopedTypeVariables #-}

module AST.Class.ZipMatch
    ( ZipMatch(..)
    , zipMatch_
    , zipMatchPure
    , doesMatch
    ) where

import           AST.Class.Children (Children(..), EmptyConstraint)
import           AST.Node (Node)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class Children expr => ZipMatch expr where
    zipMatch ::
        (Applicative f, ChildrenConstraint expr constraint) =>
        Proxy constraint ->
        (forall child. constraint child => Node a child -> Node b child -> f (Node c child)) ->
        expr a -> expr b -> Maybe (f (expr c))

-- TODO: better name for this?
zipMatchPure ::
    (ZipMatch expr, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Node a child -> Node b child -> Node c child) ->
    expr a -> expr b -> Maybe (expr c)
zipMatchPure p f x y = zipMatch p (fmap Identity . f) x y <&> runIdentity

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

doesMatch :: forall expr a b. ZipMatch expr => expr a -> expr b -> Bool
doesMatch x y =
    withDict (childrenEmptyConstraints (Proxy :: Proxy expr))
    (Lens.has Lens._Just
        (zipMatch_ (Proxy :: Proxy EmptyConstraint) (\_ _ -> Identity ()) x y))