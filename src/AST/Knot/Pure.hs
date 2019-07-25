{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies, TemplateHaskell, DeriveGeneric, DerivingStrategies #-}
module AST.Knot.Pure
    ( Pure(..), _Pure
    ) where

import           AST.Class (NodeTypesOf, HasNodeTypes)
import           AST.Class.Apply.TH (makeKApplicativeBases)
import           AST.Class.Traversable.TH (makeKTraversableAndFoldable)
import           AST.Class.ZipMatch.TH (makeZipMatch)
import           AST.Knot (Tree, Node)
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
newtype Pure k = MkPure { getPure :: Node k Pure }
    deriving stock Generic

instance HasNodeTypes Pure where
    type NodeTypesOf Pure = Pure

makeKApplicativeBases ''Pure
makeKTraversableAndFoldable ''Pure
makeZipMatch ''Pure

{-# INLINE _Pure #-}
_Pure :: Lens.Iso (Tree Pure k) (Tree Pure j) (Tree k Pure) (Tree j Pure)
_Pure = Lens.iso getPure MkPure

instance Show (Node k Pure) => Show (Pure k) where
    showsPrec p (MkPure x) = (showCon "Pure" @| x) p

instance Pretty (Node k Pure) => Pretty (Pure k) where
    pPrintPrec lvl p (MkPure x) = pPrintPrec lvl p x

deriving instance Eq  (Node k Pure) => Eq  (Pure k)
deriving instance Ord (Node k Pure) => Ord (Pure k)
instance Binary (Node k Pure) => Binary (Pure k)
instance NFData (Node k Pure) => NFData (Pure k)
