{-# LANGUAGE NoImplicitPrelude, ScopedTypeVariables, TemplateHaskell, DeriveTraversable, DeriveGeneric, FlexibleContexts, RankNTypes #-}

module AST.Knot.Ann
    ( Ann(..), ann, val
    , annotations
    , para
    ) where

import           AST.Class.Children (Children(..), overChildren)
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import           AST.Node (Node)
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Constraint
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import           Prelude.Compat

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
    forall e a b.
    Recursive Children e =>
    Lens.Traversal
    (Node (Ann a) e)
    (Node (Ann b) e)
    a b
annotations f (Ann pl x) =
    withDict (recursive :: Dict (RecursiveConstraint e Children)) $
    Ann <$> f pl <*> children (Proxy :: Proxy (Recursive Children)) (annotations f) x

-- Similar to `para` from `recursion-schemes`,
-- except it's int term of full annotated trees rather than just the final result.
-- TODO: What does the name `para` mean?
para ::
    forall constraint expr a.
    Recursive constraint expr =>
    Proxy constraint ->
    (forall child. Recursive constraint child => child (Ann a) -> a) ->
    Node Identity expr ->
    Node (Ann a) expr
para p f x =
    Ann (f r) r
    where
        r :: expr (Ann a)
        r =
            withDict (recursive :: Dict (RecursiveConstraint expr constraint)) $
            overChildren (Proxy :: Proxy (Recursive constraint))
            (para p f) (runIdentity x)
