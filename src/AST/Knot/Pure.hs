{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TemplateHaskell, DeriveGeneric, DerivingStrategies #-}
module AST.Knot.Pure
    ( Pure(..), _Pure
    ) where

import           AST.Class.Children.TH (makeChildren)
import           AST.Class.ZipMatch.TH (makeZipMatch)
import           AST.Knot (Tie, Tree)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Text.Show.Combinators ((@|), showCon)

import           Prelude.Compat

-- Prefer using the _Pure Iso to the MkPure data constructor, because "MkPure"
-- cannot tell the type checker that "k" is of the form "Knot j", which makes
-- type inference brittle. The Iso tells the type-checker that.
newtype Pure k = MkPure { getPure :: Tie k Pure }
    deriving stock Generic
makeChildren ''Pure
makeZipMatch ''Pure

{-# INLINE _Pure #-}
_Pure :: Lens.Iso (Tree Pure k) (Tree Pure j) (Tree k Pure) (Tree j Pure)
_Pure = Lens.iso getPure MkPure

instance Show (Tie k Pure) => Show (Pure k) where
    showsPrec p (MkPure x) = (showCon "Pure" @| x) p

instance Pretty (Tie k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (MkPure x) = pPrintPrec lvl p x

deriving instance Eq  (Tie k Pure) => Eq  (Pure k)
deriving instance Ord (Tie k Pure) => Ord (Pure k)
instance Binary (Tie k Pure) => Binary (Pure k)
instance NFData (Tie k Pure) => NFData (Pure k)
