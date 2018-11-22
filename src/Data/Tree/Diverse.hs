{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, RankNTypes, TemplateHaskell #-}

module Data.Tree.Diverse
    ( Node, Children(..), overChildren
    , leaf, hoist
    , Ann(..), ann, val
    , annotations
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

-- Annotate tree nodes
data Ann a v = Ann
    { _ann :: a
    , _val :: v
    } deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
instance (Binary a, Binary v) => Binary (Ann a v)
Lens.makeLenses ''Ann

instance (Pretty a, Pretty v) => Pretty (Ann a v) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotations ::
    Children e =>
    Lens.Traversal
    (Node (Ann a) e)
    (Node (Ann b) e)
    a b
annotations f (Ann pl x) = Ann <$> f pl <*> children (annotations f) x
