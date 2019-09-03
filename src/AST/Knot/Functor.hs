-- | Functors as Knots
{-# LANGUAGE TemplateHaskell, FlexibleInstances, UndecidableInstances, GADTs #-}
module AST.Knot.Functor
    ( F(..), _F, KWitness(..)
    ) where

import AST.Class.Nodes (KNodes(..))
import AST.Class.Recursive (RNodes, RFunctor, RFoldable, RTraversable)
import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import GHC.Generics (Generic)

import Prelude.Compat

-- | Lift a 'Functor', or type constructor of kind @Type -> Type@ to a 'AST.Knot.Knot'.
--
-- * @F Maybe@ can be used to encode structures with missing values
-- * @F (Either Text)@ can be used to encode results of parsing where structure components
--   may fail to parse.
newtype F f k = F (f (Node k (F f)))
    deriving stock Generic

-- | An 'Iso' from 'F' to its content.
--
-- Using `_F` rather than the 'F' data constructor is recommended,
-- because it helps the type inference know that @F f@ is parameterized with a 'AST.Knot.Knot'.
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
