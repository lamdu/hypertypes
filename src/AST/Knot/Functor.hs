-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}
module AST.Knot.Functor
    ( ToKnot(..), _ToKnot
    ) where

import AST.Class.Recursive
import AST.Knot (Tree, Node)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Data.Binary (Binary)
import Generics.OneLiner (Constraints)
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

makeKTraversableApplyAndBases ''ToKnot

instance RNodes (ToKnot f)
instance Functor f => RFunctor (ToKnot f)
instance Foldable f => RFoldable (ToKnot f)
instance Traversable f => RTraversable (ToKnot f)

deriving instance Constraints (ToKnot f k) Eq   => Eq   (ToKnot f k)
deriving instance Constraints (ToKnot f k) Ord  => Ord  (ToKnot f k)
deriving instance Constraints (ToKnot f k) Show => Show (ToKnot f k)
instance Constraints (ToKnot f k) Binary => Binary (ToKnot f k)
instance Constraints (ToKnot f k) NFData => NFData (ToKnot f k)
