{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TemplateHaskell #-}

module AST.Knot.Pure
    ( Pure(..), _Pure
    ) where

import AST.Class.Children.TH (makeChildren)
import AST.Knot (Tie)
import Control.Lens (makePrisms)
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Text.Show.Combinators ((@|), showCon)

import Prelude.Compat

newtype Pure k = Pure { getPure :: Tie k Pure }
makePrisms ''Pure
makeChildren ''Pure

deriving instance Eq  (Tie k Pure) => Eq  (Pure k)
deriving instance Ord (Tie k Pure) => Ord (Pure k)

instance Show (Tie k Pure) => Show (Pure k) where
    showsPrec p (Pure x) = (showCon "Pure" @| x) p

instance Pretty (Tie k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (Pure x) = pPrintPrec lvl p x
