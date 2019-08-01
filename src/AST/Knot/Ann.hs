{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, StandaloneDeriving, RankNTypes #-}
{-# LANGUAGE DeriveGeneric, FlexibleContexts, TypeFamilies, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, ConstraintKinds, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations, annotationsWith
    , strip, addAnnotations
    ) where

import           AST.Class
import           AST.Class.Recursive
import           AST.Class.Traversable
import           AST.Class.Traversable.TH (makeKTraversableAndBases)
import           AST.Class.ZipMatch.TH (makeZipMatch)
import           AST.Combinator.ANode (ANode)
import           AST.Knot (Tree, Node)
import           AST.Knot.Dict
import           AST.Knot.Pure (Pure(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, Dict(..), withDict)
import           Data.Constraint.List (ApplyConstraints)
import           Data.Proxy (Proxy(..))
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
    type NodeTypesOf (Ann a) = ANode (Ann a)

makeKTraversableAndBases ''Ann
makeZipMatch ''Ann

instance c (Ann a) => Recursively c (Ann a)

instance Deps Pretty a t => Pretty (Ann a t) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotationsWithDict ::
    forall k cs a b.
    Tree (RecursiveNodes k) (KDict cs) ->
    (forall n. ApplyConstraints cs n => Dict (KTraversable n)) ->
    Traversal
    (Tree (Ann a) k)
    (Tree (Ann b) k)
    a b
annotationsWithDict c getTraversable f (Ann pl x) =
    withDict (c ^. recSelf . _KDict) $
    withDict (getTraversable :: Dict (KTraversable k)) $
    Ann
    <$> f pl
    <*> traverseKRec c (\d -> annotationsWithDict d getTraversable f) x

annotationsWith ::
    forall k cs a b.
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyConstraints cs n => Dict (KTraversable n)) ->
    Traversal
    (Tree (Ann a) k)
    (Tree (Ann b) k)
    a b
annotationsWith _ =
    annotationsWithDict (rLiftConstraints :: Tree (RecursiveNodes k) (KDict cs))

annotations ::
    (Recursively KNodes e, Recursively KTraversable e) =>
    Traversal
    (Tree (Ann a) e)
    (Tree (Ann b) e)
    a b
annotations = annotationsWith (Proxy :: Proxy '[KTraversable]) Dict

strip ::
    (Recursively KNodes expr, Recursively KTraversable expr) =>
    Tree (Ann a) expr ->
    Tree Pure expr
strip = unwrap (Proxy :: Proxy '[KTraversable]) Dict (^. val)

addAnnotations ::
    RLiftConstraints k cs =>
    Proxy cs ->
    (forall n. ApplyConstraints cs n => Dict (KFunctor n)) ->
    (forall n. ApplyConstraints cs n => Tree n (Ann a) -> a) ->
    Tree Pure k -> Tree (Ann a) k
addAnnotations p getFunctor f = wrap p getFunctor (\x -> Ann (f x) x)

type Deps c a t = ((c a, c (Node t (Ann a))) :: Constraint)
deriving instance Deps Eq   a t => Eq   (Ann a t)
deriving instance Deps Ord  a t => Ord  (Ann a t)
deriving instance Deps Show a t => Show (Ann a t)
instance Deps Binary a t => Binary (Ann a t)
instance Deps NFData a t => NFData (Ann a t)
