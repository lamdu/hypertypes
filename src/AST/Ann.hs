{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, DeriveTraversable, TemplateHaskell, ScopedTypeVariables #-}

module AST.Ann
    ( Ann(..), ann, val
    , annotations
    ) where

import           AST
import           AST.Recursive
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Constraint
import           Data.Proxy
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
    Recursive e =>
    Lens.Traversal
    (Node (Ann a) e)
    (Node (Ann b) e)
    a b
annotations f (Ann pl x) =
    withDict (recursive (Proxy :: Proxy e))
    (Ann <$> f pl <*> children (Proxy :: Proxy Recursive) (annotations f) x)
