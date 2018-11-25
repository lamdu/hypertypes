{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes, ConstraintKinds, FlexibleInstances, UndecidableInstances, UndecidableSuperClasses #-}

module AST
    ( Node, Children(..), traverseChildren, overChildren
    , ConstrainedNodeTraversal(..)
    , leaf, hoist
    ) where

import           Control.Lens (Lens)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy
import           GHC.Exts (Constraint)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type Node f expr = f (expr f)

newtype ConstrainedNodeTraversal constraint f n m =
    CNTraversal (forall expr. constraint expr => Node n expr -> f (Node m expr))

class ChildrenConstraint expr Children => Children expr where
    type ChildrenTraversal expr (f :: * -> *) (n :: * -> *) (m :: * -> *)
    type ChildrenConstraint expr (constraint :: ((* -> *) -> *) -> Constraint) :: Constraint
    children ::
        (Applicative f, Functor n, Functor m) =>
        ChildrenTraversal expr f n m ->
        expr n -> f (expr m)
    liftChildrenTraversal ::
        ChildrenConstraint expr constraint =>
        Proxy constraint ->
        Proxy (expr n) ->
        Proxy (f (expr m)) ->
        ConstrainedNodeTraversal constraint f n m ->
        ChildrenTraversal expr f n m

traverseChildren ::
    (ChildrenConstraint expr constraint, Children expr, Applicative f, Functor n, Functor m) =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> f (Node m child)) ->
    expr n -> f (expr m)
traverseChildren pc f =
    case (Proxy, Proxy) of
    (pi, po) ->
        (`asProxyTypeOf` po) .
        children (liftChildrenTraversal pc pi po (CNTraversal f)) . (`asProxyTypeOf` pi)

overChildren ::
    (ChildrenConstraint expr constraint, Children expr, Functor n, Functor m) =>
    Proxy constraint ->
    (forall child. constraint child => Node n child -> Node m child) ->
    expr n -> expr m
overChildren pc f =
    case (Proxy, Proxy) of
    (pi, po) ->
        runIdentity .
        (`asProxyTypeOf` po) .
        children (liftChildrenTraversal pc pi po (CNTraversal (Identity . f))) .
        (`asProxyTypeOf` pi)

instance Children (Const val) where
    type ChildrenTraversal (Const val) f n m = ()
    type ChildrenConstraint (Const val) constraint = ()
    children _ (Const x) = pure (Const x)
    liftChildrenTraversal _ _ _ _ = ()

leaf ::
    (Functor n, Functor m) =>
    Lens (n a) (m b) (Node n (Const a)) (Node m (Const b))
leaf f x =
    x
    <&> Lens.Const
    & f
    <&> fmap Lens.getConst

hoist ::
    (Children expr, Functor f, Functor g) =>
    (forall a. f a -> g a) ->
    expr f -> expr g
hoist f = overChildren (Proxy :: Proxy Children) (f . fmap (hoist f))
