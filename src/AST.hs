{-# LANGUAGE NoImplicitPrelude, RankNTypes #-}

module AST
    ( Node, Children(..), overChildren
    , leaf, hoist
    ) where

import           Control.Lens (Lens)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

type Node f expr = f (expr f)

class Children expr where
    children ::
        (Applicative f, Functor n, Functor m) =>
        (forall sub. Children sub => Node n sub -> f (Node m sub)) ->
        expr n -> f (expr m)

overChildren ::
    (Children expr, Functor n, Functor m) =>
    (forall sub. Children sub => Node n sub -> Node m sub) ->
    expr n -> expr m
overChildren f = runIdentity . children (Identity . f)

instance Children (Const val) where
    children _ (Const x) = pure (Const x)

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
