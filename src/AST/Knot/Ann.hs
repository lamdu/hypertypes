{-# LANGUAGE TemplateHaskell, RankNTypes, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations
    , strip, addAnnotations
    ) where

import           AST.Class
import           AST.Class.Recursive
import           AST.Class.Traversable
import           AST.Knot (Tree, Node)
import           AST.Knot.Pure (Pure(..))
import           AST.TH.Traversable (makeKTraversableAndBases)
-- import           AST.TH.ZipMatch (makeZipMatch)
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Dict(..), withDict)
-- import           Data.Functor.Product.PolyKinds (Product(..))
import           Data.Proxy (Proxy(..))
import           Generics.OneLiner (Constraints)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- Annotate tree nodes
data Ann a knot = Ann
    { _ann :: a
    , _val :: Node knot (Ann a)
    } deriving Generic
makeLenses ''Ann

instance KNodes (Ann a) where
    type instance NodesConstraint (Ann a) c = c (Ann a)
    {-# INLINE kCombineConstraints #-}
    kCombineConstraints _ = Dict

makeKTraversableAndBases ''Ann
-- makeZipMatch ''Ann

instance Monoid a => KPointed (Ann a) where
    pureK = Ann mempty
    pureKWith _ = Ann mempty

-- instance Monoid a => KApply (Ann a) where
--     zipK (Ann a0 v0) (Ann a1 v1) = Ann (a0 <> a1) (Pair v0 v1)

instance Constraints (Ann a t) Pretty => Pretty (Ann a t) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotations ::
    forall k a b.
    RTraversable k =>
    Traversal
    (Tree (Ann a) k)
    (Tree (Ann b) k)
    a b
annotations f (Ann pl x) =
    withDict (recurse (Proxy @(RTraversable k))) $
    Ann
    <$> f pl
    <*> traverseKWith (Proxy @RTraversable) (annotations f) x

strip ::
    RTraversable expr =>
    Tree (Ann a) expr ->
    Tree Pure expr
strip = unwrap (Proxy @RTraversable) Dict (^. val)

addAnnotations ::
    (Recursive c, RNodes k, c k) =>
    Proxy c ->
    (forall n. c n => Dict (KFunctor n)) ->
    (forall n. c n => Tree n (Ann a) -> a) ->
    Tree Pure k -> Tree (Ann a) k
addAnnotations p getFunctor f = wrap p getFunctor (\x -> Ann (f x) x)

deriving instance Constraints (Ann a t) Eq   => Eq   (Ann a t)
deriving instance Constraints (Ann a t) Ord  => Ord  (Ann a t)
deriving instance Constraints (Ann a t) Show => Show (Ann a t)
instance Constraints (Ann a t) Binary => Binary (Ann a t)
instance Constraints (Ann a t) NFData => NFData (Ann a t)
