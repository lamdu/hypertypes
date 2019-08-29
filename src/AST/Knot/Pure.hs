{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}
module AST.Knot.Pure
    ( Pure(..), _Pure, (&#)
    ) where

import           AST.Knot (Tree, Node)
import           AST.TH.Traversable (makeKTraversableApplyAndBases)
import           AST.TH.ZipMatch (makeZipMatch)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Generics.Constraints (makeDerivings, makeInstances)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Text.Show.Combinators ((@|), showCon)

import           Prelude.Compat

-- Prefer using the _Pure Iso to the Pure data constructor, because "Pure"
-- cannot tell the type checker that "k" is of the form "Knot j", which makes
-- type inference brittle. The Iso tells the type-checker that.
newtype Pure k = Pure { getPure :: Node k Pure }
    deriving stock Generic

makeKTraversableApplyAndBases ''Pure
makeZipMatch ''Pure
makeDerivings [''Eq, ''Ord] [''Pure]
makeInstances [''Binary, ''NFData] [''Pure]

{-# INLINE _Pure #-}
_Pure :: Lens.Iso (Tree Pure k) (Tree Pure j) (Tree k Pure) (Tree j Pure)
_Pure = Lens.iso getPure Pure

infixl 1 &#
{-# INLINE (&#) #-}
(&#) :: a -> (a -> Tree k Pure) -> Tree Pure k
x &# f = _Pure # f x

instance Show (Node k Pure) => Show (Pure k) where
    showsPrec p (Pure x) = (showCon "Pure" @| x) p

instance Pretty (Node k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (Pure x) = pPrintPrec lvl p x
