{-# LANGUAGE TemplateHaskell, RankNTypes, UndecidableInstances, GADTs #-}

module AST.Knot.Ann
    ( Ann(..), ann, val, KWitness(..)
    , annotations
    , strip, addAnnotations
    ) where

import           AST.Class.Functor (mapK)
import           AST.Class.Monad
import           AST.Class.Nodes (KNodes(..), (#>))
import           AST.Class.Recursive
import           AST.Class.Traversable (traverseK)
import           AST.Combinator.Compose
import           AST.Knot (Tree, Node)
import           AST.Knot.Pure (Pure(..))
import           AST.TH.Traversable (makeKTraversableApplyAndBases)
import           AST.TH.ZipMatch (makeZipMatch)
import           AST.TH.Internal.Instances (makeCommonInstances)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A 'AST.Knot.Knot' which adds an annotation to every node in a tree
data Ann a k = Ann
    { _ann :: a
    , _val :: Node k (Ann a)
    } deriving Generic
makeLenses ''Ann

makeCommonInstances [''Ann]
makeKTraversableApplyAndBases ''Ann
makeZipMatch ''Ann

instance RNodes (Ann a)
instance RFunctor (Ann a)
instance RFoldable (Ann a)
instance RTraversable (Ann a)

instance Monoid a => KMonad (Ann a) where
    joinK (MkCompose (Ann a0 (MkCompose (Ann a1 (MkCompose x))))) =
        Ann (a0 <> a1) (t x)
        where
            t ::
                forall p.
                RFunctor p =>
                Tree p (Compose (Ann a) (Ann a)) ->
                Tree p (Ann a)
            t =
                withDict (recurse (Proxy @(RFunctor p))) $
                mapK (Proxy @RFunctor #> joinK)

instance Constraints (Ann a t) Pretty => Pretty (Ann a t) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

-- | A 'Traversal' from an annotated tree to its annotations
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
    <*> traverseK (Proxy @RTraversable #> annotations f) x

-- | Remove a tree's annotations
strip ::
    RFunctor expr =>
    Tree (Ann a) expr ->
    Tree Pure expr
strip = unwrap (Proxy @RFunctor) (^. val)

-- | Compute annotations for a tree from the bottom up
addAnnotations ::
    (Recursive c, RFunctor k, c k) =>
    Proxy c ->
    (forall n. c n => Tree n (Ann a) -> a) ->
    Tree Pure k -> Tree (Ann a) k
addAnnotations p f = wrap p (\x -> Ann (f x) x)
