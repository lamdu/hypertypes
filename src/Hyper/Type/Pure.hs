-- | A 'Hyper.Type.AHyperType' to express the simplest plain form of a nested higher-kinded data structure.
--
-- The value level [hyperfunctions](http://hackage.haskell.org/package/hyperfunctions)
-- equivalent of 'Pure' is called @self@ in
-- [Hyperfunctions papers](https://arxiv.org/abs/1309.5135).

{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}
module Hyper.Type.Pure
    ( Pure(..), _Pure, HWitness(..)
    , (&#)
    ) where

import Control.Lens (Iso, iso)
import Control.Lens.Operators
import GHC.Generics (Generic)
import Hyper.Class.Nodes (HNodes(..))
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.TH.Traversable (makeHTraversableApplyAndBases)
import Hyper.Type (Tree, type (#))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

-- | A 'Hyper.Type.AHyperType' to express the simplest plain form of a nested higher-kinded data structure
newtype Pure k = Pure (k # Pure)
    deriving stock Generic

makeHTraversableApplyAndBases ''Pure
makeCommonInstances [''Pure]

-- | An 'Iso' from 'Pure' to its content.
--
-- Using `_Pure` rather than the 'Pure' data constructor is recommended,
-- because it helps the type inference know that 'Pure' is parameterized with a 'Hyper.Type.AHyperType'.
{-# INLINE _Pure #-}
_Pure :: Iso (Tree Pure k) (Tree Pure j) (Tree k Pure) (Tree j Pure)
_Pure = iso (\(Pure x) -> x) Pure

-- | An operator to apply a function to a value and wrap it with 'Pure'.
--
-- Helps value construction be more succinct.
--
-- The etymology and fixity of '&#' operator mimics '&'.
--
-- >>> x &# f
-- Pure (f x)
infixl 1 &#
{-# INLINE (&#) #-}
(&#) :: a -> (a -> Tree k Pure) -> Tree Pure k
x &# f = _Pure # f x

instance Pretty (k # Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (Pure x) = pPrintPrec lvl p x
