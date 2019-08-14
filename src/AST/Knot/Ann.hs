{-# LANGUAGE TemplateHaskell, RankNTypes, UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, ScopedTypeVariables #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations, annotationsWith
    , strip, addAnnotations
    ) where

import           AST.Class
import           AST.Class.Combinators
import           AST.Class.Monad
import           AST.Class.Recursive
import           AST.Class.Traversable
import           AST.Combinator.ANode (ANode)
import           AST.Combinator.Compose
import           AST.Knot (Tree, Node)
import           AST.Knot.Dict
import           AST.Knot.Pure (Pure(..))
import           AST.TH.Traversable (makeKTraversableAndBases)
import           AST.TH.ZipMatch (makeZipMatch)
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, Dict(..), withDict)
import           Data.Constraint.List (ApplyConstraints)
import           Data.Functor.Product.PolyKinds (Product(..))
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
    {-# INLINE combineConstraints #-}
    combineConstraints _ _ _ = Dict

makeKTraversableAndBases ''Ann
makeZipMatch ''Ann

instance Monoid a => KPointed (Ann a) where
    pureK = Ann mempty
    pureKWithConstraint _ = Ann mempty

instance Monoid a => KApply (Ann a) where
    zipK (Ann a0 v0) (Ann a1 v1) = Ann (a0 <> a1) (Pair v0 v1)

instance Monoid a => KMonad (Ann a) where
    joinK (MkCompose (Ann a0 (MkCompose (Ann a1 (MkCompose x))))) =
        withDict (r x) $
        mapKWith (Proxy @'[Recursively KFunctor]) joinK x
        & Ann (a0 <> a1)
        where
            r :: Recursively KFunctor l => Tree l k -> RecursiveDict l KFunctor
            r _ = recursive

instance c (Ann a) => Recursively c (Ann a) where
    {-# INLINE combineRecursive #-}
    combineRecursive = Dict

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
    withDict (getTraversable @k) $
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
annotationsWith _ = annotationsWithDict (rLiftConstraints @k @cs)

annotations ::
    (Recursively KNodes e, Recursively KTraversable e) =>
    Traversal
    (Tree (Ann a) e)
    (Tree (Ann b) e)
    a b
annotations = annotationsWith (Proxy @'[KTraversable]) Dict

strip ::
    (Recursively KNodes expr, Recursively KTraversable expr) =>
    Tree (Ann a) expr ->
    Tree Pure expr
strip = unwrap (Proxy @'[KTraversable]) Dict (^. val)

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
