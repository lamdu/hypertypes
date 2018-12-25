{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, TemplateHaskell, DeriveGeneric, FlexibleContexts, RankNTypes, TypeFamilies, MultiParamTypeClasses, UndecidableInstances, ConstraintKinds, StandaloneDeriving #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations
    , para
    ) where

import           AST.Class.Children (Children(..), overChildren)
import           AST.Class.Recursive (Recursive(..), RecursiveDict)
import           AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import           AST.Knot (Tie, Tree)
import           AST.Knot.Pure (Pure(..))
import           Control.DeepSeq (NFData)
import           Control.Lens (Traversal, makeLenses)
import           Data.Binary (Binary)
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

-- Annotate tree nodes
data Ann a knot = Ann
    { _ann :: a
    , _val :: Tie knot (Ann a)
    } deriving Generic
makeLenses ''Ann

makeChildrenAndZipMatch [''Ann]

type AnnConstraints c a t = (c a, SubTreeConstraint (Ann a) t c)

deriving instance AnnConstraints Eq   a t => Eq   (Ann a t)
deriving instance AnnConstraints Ord  a t => Ord  (Ann a t)
deriving instance AnnConstraints Show a t => Show (Ann a t)

instance AnnConstraints Binary a t => Binary (Ann a t)
instance AnnConstraints NFData a t => NFData (Ann a t)

instance AnnConstraints Pretty a t => Pretty (Ann a t) where
    pPrintPrec lvl prec (Ann pl b)
        | PP.isEmpty plDoc || plDoc == PP.text "()" = pPrintPrec lvl prec b
        | otherwise =
            maybeParens (13 < prec) $ mconcat
            [ pPrintPrec lvl 14 b, PP.text "{", plDoc, PP.text "}" ]
        where
            plDoc = pPrintPrec lvl 0 pl

annotations ::
    forall e a b.
    Recursive Children e =>
    Traversal
    (Tree (Ann a) e)
    (Tree (Ann b) e)
    a b
annotations f (Ann pl x) =
    withDict (recursive :: RecursiveDict Children e) $
    Ann <$> f pl <*> children (Proxy :: Proxy (Recursive Children)) (annotations f) x

-- Similar to `para` from `recursion-schemes`,
-- except it's int term of full annotated trees rather than just the final result.
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
            withDict (recursive :: RecursiveDict constraint expr) $
            overChildren (Proxy :: Proxy (Recursive constraint))
            (para p f) (getPure x)
