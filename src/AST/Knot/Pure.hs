{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TemplateHaskell, DeriveGeneric #-}

module AST.Knot.Pure
    ( Pure(..), _Pure
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Knot (Tie)
import Control.DeepSeq (NFData)
import Control.Lens (makePrisms)
import Data.Binary (Binary)
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Text.Show.Combinators ((@|), showCon)

import Prelude.Compat

newtype Pure k = Pure { getPure :: Tie k Pure }
    deriving Generic
makePrisms ''Pure
makeChildren ''Pure

instance Show (Tie k Pure) => Show (Pure k) where
    showsPrec p (Pure x) = (showCon "Pure" @| x) p

instance Pretty (Tie k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (Pure x) = pPrintPrec lvl p x

deriving instance Eq  (Tie k Pure) => Eq  (Pure k)
deriving instance Ord (Tie k Pure) => Ord (Pure k)
instance Binary (Tie k Pure) => Binary (Pure k)
instance NFData (Tie k Pure) => NFData (Pure k)
