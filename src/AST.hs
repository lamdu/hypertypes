{-# LANGUAGE NoImplicitPrelude, TypeFamilies, RankNTypes #-}

module AST
    ( Node, Children(..), traverseChildren, overChildren
    , leaf, hoist
    ) where

import           Control.Lens (Lens)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type Node f expr = f (expr f)

class Children expr where
    type ChildrenTraversal expr (f :: * -> *) (n :: * -> *) (m :: * -> *)
    children ::
        (Applicative f, Functor n, Functor m) =>
        ChildrenTraversal expr f n m ->
        expr n -> f (expr m)
    liftChildrenTraversal ::
        Proxy (expr n) ->
        (forall sub. Children sub => Node n sub -> f (Node m sub)) ->
        ChildrenTraversal expr f n m

traverseChildren ::
    (Children expr, Applicative f, Functor n, Functor m) =>
    (forall sub. Children sub => Node n sub -> f (Node m sub)) ->
    expr n -> f (expr m)
traverseChildren f =
    case Proxy of
    p -> children (liftChildrenTraversal p f) . (`asProxyTypeOf` p)

overChildren ::
    (Children expr, Functor n, Functor m) =>
    (forall sub. Children sub => Node n sub -> Node m sub) ->
    expr n -> expr m
overChildren f =
    case Proxy of
    p -> runIdentity . children (liftChildrenTraversal p (Identity . f)) . (`asProxyTypeOf` p)

instance Children (Const val) where
    type ChildrenTraversal (Const val) f n m = ()
    children _ (Const x) = pure (Const x)
    liftChildrenTraversal _ _ = ()

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
hoist f = overChildren (f . fmap (hoist f))
