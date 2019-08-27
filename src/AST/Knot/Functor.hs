-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}
module AST.Knot.Functor
    ( ToKnot(..), _ToKnot
    ) where

import AST.Class.Recursive
import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

import Prelude.Compat

newtype ToKnot f k = MkToKnot (f (Node k (ToKnot f)))
    deriving stock Generic

_ToKnot ::
    Iso (Tree (ToKnot f0) k0)
        (Tree (ToKnot f1) k1)
        (f0 (Tree k0 (ToKnot f0)))
        (f1 (Tree k1 (ToKnot f1)))
_ToKnot = iso (\(MkToKnot x) -> x) MkToKnot

makeCommonInstances ''ToKnot
makeKTraversableApplyAndBases ''ToKnot

instance RNodes (ToKnot f)
instance Functor f => RFunctor (ToKnot f)
instance Foldable f => RFoldable (ToKnot f)
instance Traversable f => RTraversable (ToKnot f)
