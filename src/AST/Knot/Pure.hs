{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}
module AST.Knot.Pure
    ( Pure(..), _Pure
    , (&#)
    ) where

import AST.Knot (Tree, Node)
import AST.TH.Internal.Instances (makeCommonInstances)
import AST.TH.Traversable (makeKTraversableApplyAndBases)
import Control.Lens (Iso, iso)
import Control.Lens.Operators
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJClass (Pretty(..))

-- | A 'AST.Knot.Knot' to express the simplest plain form of a nested higher-kinded data structure.
--
-- The value level [hyperfunctions](http://hackage.haskell.org/package/hyperfunctions)
-- equivalent of 'Pure' is called @self@ in
-- [Hyperfunctions papers](https://arxiv.org/abs/1309.5135).
newtype Pure k = Pure (Node k Pure)
    deriving stock Generic

makeKTraversableApplyAndBases ''Pure
makeCommonInstances [''Pure]

-- | An 'Iso' from 'Pure' to its content.
--
-- Using `_Pure` rather than the 'Pure' data constructor is recommended,
-- because it helps the type inference know that 'Pure' is parameterized with a 'AST.Knot.Knot'.
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

instance Pretty (Node k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (Pure x) = pPrintPrec lvl p x
