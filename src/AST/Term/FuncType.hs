{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

module AST.Term.FuncType
    ( FuncType(..), funcIn, funcOut
    , HasFuncType(..)
    ) where

import           AST
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism', makeLenses)
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           GHC.Generics (Generic)
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           Text.Show.Combinators ((@|), showCon)

import           Prelude.Compat

data FuncType typ k = FuncType
    { _funcIn  :: Node k typ
    , _funcOut :: Node k typ
    } deriving Generic

makeLenses ''FuncType
makeZipMatch ''FuncType
makeKTraversableApplyAndBases ''FuncType

instance Pretty (Node k typ) => Pretty (FuncType typ k) where
    pPrintPrec lvl p (FuncType i o) =
        pPrintPrec lvl 11 i <+> Pretty.text "->" <+> pPrintPrec lvl 10 o
        & maybeParens (p > 10)

instance Show (Node k typ) => Show (FuncType typ k) where
    showsPrec p (FuncType i o) = (showCon "FuncType" @| i @| o) p

class HasFuncType typ where
    funcType :: Prism' (Tree typ k) (Tree (FuncType typ) k)

deriving instance Eq  (Node k typ) => Eq  (FuncType typ k)
deriving instance Ord (Node k typ) => Ord (FuncType typ k)
instance Binary (Node k typ) => Binary (FuncType typ k)
instance NFData (Node k typ) => NFData (FuncType typ k)
