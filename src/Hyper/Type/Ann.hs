-- | A 'Hyper.Type.Knot' which adds an annotation to every node in a tree

{-# LANGUAGE TemplateHaskell, UndecidableInstances, FlexibleInstances, FlexibleContexts #-}

module Hyper.Type.Ann
    ( Ann(..), ann, val, KWitness(..)
    , annotations
    , strip, addAnnotations
    ) where

import           Hyper.Class.Functor (KFunctor(..))
import           Hyper.Class.Monad
import           Hyper.Class.Nodes (KNodes(..), (#>))
import           Hyper.Class.Traversable (traverseK)
import           Hyper.Combinator.Compose
import           Hyper.Type (Tree, type (#))
import           Hyper.Type.Pure (Pure(..))
import           Hyper.Recurse
import           Hyper.TH.Traversable (makeKTraversableApplyAndBases)
import           Hyper.TH.ZipMatch (makeZipMatch)
import           Hyper.TH.Internal.Instances (makeCommonInstances)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import           Generics.Constraints (Constraints)
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- | A 'Hyper.Type.Knot' which adds an annotation to every node in a tree
data Ann a k = Ann
    { _ann :: a
    , _val :: k # Ann a
    } deriving Generic
makeLenses ''Ann

makeCommonInstances [''Ann]
makeKTraversableApplyAndBases ''Ann
makeZipMatch ''Ann

instance c (Ann a) => Recursively c (Ann a)
instance RNodes (Ann a)
instance RTraversable (Ann a)

instance Monoid a => KMonad (Ann a) where
    joinK (MkCompose (Ann a0 (MkCompose (Ann a1 (MkCompose x))))) =
        Ann (a0 <> a1) (t x)
        where
            t ::
                forall p.
                Recursively KFunctor p =>
                Tree p (Compose (Ann a) (Ann a)) ->
                Tree p (Ann a)
            t =
                withDict (recursively (Proxy @(KFunctor p))) $
                mapK (Proxy @(Recursively KFunctor) #> joinK)

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
    Recursively KFunctor expr =>
    Tree (Ann a) expr ->
    Tree Pure expr
strip = unwrap (const (^. val))

-- | Compute annotations for a tree from the bottom up
addAnnotations ::
    Recursively KFunctor k =>
    (forall n. KRecWitness k n -> Tree n (Ann a) -> a) ->
    Tree Pure k ->
    Tree (Ann a) k
addAnnotations f = wrap (\w x -> Ann (f w x) x)
