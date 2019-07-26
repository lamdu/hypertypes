{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, StandaloneDeriving, RankNTypes #-}
{-# LANGUAGE DeriveGeneric, FlexibleContexts, TypeFamilies, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, ConstraintKinds, DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations, annotationsWith
    , strip, addAnnotations
    , para
    ) where

import           AST.Class (HasNodes(..))
import           AST.Class.Combinators (mapKWith)
import           AST.Class.Recursive (Recursive(..), RecursiveDict, wrap, unwrap, recursiveChildren)
import           AST.Class.Traversable
import           AST.Class.Traversable.TH (makeKTraversableAndBases)
import           AST.Class.ZipMatch.TH (makeZipMatch)
import           AST.Constraint
import           AST.Combinator.Single (Single)
import           AST.Knot (Tree, Node)
import           AST.Knot.Pure (Pure(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal, makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (Constraint, withDict)
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

instance HasNodes (Ann a) where
    type NodeTypesOf (Ann a) = Single (Ann a)
    type NodesConstraint (Ann a) = KnotsConstraint '[Ann a]

makeKTraversableAndBases ''Ann
makeZipMatch ''Ann

instance c (Ann a) => Recursive c (Ann a)

instance Deps Pretty a t => Pretty (Ann a t) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotationsWith ::
    Recursive constraint e =>
    Proxy constraint ->
    Traversal
    (Tree (Ann a) e)
    (Tree (Ann b) e)
    a b
annotationsWith p f (Ann pl x) =
    Ann
    <$> f pl
    <*> recursiveChildren p (annotationsWith p f) x

annotations ::
    Recursive KTraversable e =>
    Traversal
    (Tree (Ann a) e)
    (Tree (Ann b) e)
    a b
annotations = annotationsWith (Proxy :: Proxy KTraversable)

-- Similar to `para` from `recursion-schemes`,
-- except it's in terms of full annotated trees rather than just the final result.
-- TODO: What does the name `para` mean?
para ::
    forall constraint expr a.
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. Recursive constraint child => Tree child (Ann a) -> a) ->
    Tree Pure expr ->
    Tree (Ann a) expr
para p f x =
    Ann (f r) r
    where
        r =
            withDict (recursive :: RecursiveDict expr constraint) $
            mapKWith (Proxy :: Proxy '[Recursive constraint]) (para p f) (getPure x)

strip :: Recursive KTraversable expr => Tree (Ann a) expr -> Tree Pure expr
strip = unwrap (Proxy :: Proxy KTraversable) (^. val)

addAnnotations ::
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. constraint child => Tree child (Ann a) -> a) ->
    Tree Pure expr -> Tree (Ann a) expr
addAnnotations p f = wrap p (\x -> Ann (f x) x)

type Deps c a t = ((c a, c (Node t (Ann a))) :: Constraint)
deriving instance Deps Eq   a t => Eq   (Ann a t)
deriving instance Deps Ord  a t => Ord  (Ann a t)
deriving instance Deps Show a t => Show (Ann a t)
instance Deps Binary a t => Binary (Ann a t)
instance Deps NFData a t => NFData (Ann a t)
