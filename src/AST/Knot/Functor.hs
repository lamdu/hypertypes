-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances #-}
module AST.Knot.Functor
    ( F(..), _F
    ) where

import AST.Class.Recursive
import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

import Prelude.Compat

newtype F f k = F (f (Node k (F f)))
    deriving stock Generic

_F ::
    Iso (Tree (F f0) k0)
        (Tree (F f1) k1)
        (f0 (Tree k0 (F f0)))
        (f1 (Tree k1 (F f1)))
_F = iso (\(F x) -> x) F

makeCommonInstances [''F]
makeKTraversableApplyAndBases ''F

instance RNodes (F f)
instance Functor f => RFunctor (F f)
instance Foldable f => RFoldable (F f)
instance Traversable f => RTraversable (F f)
