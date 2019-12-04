{-# LANGUAGE UndecidableInstances, TemplateHaskell, FlexibleInstances #-}

module Hyper.Type.AST.FuncType
    ( FuncType(..), funcIn, funcOut, W_FuncType(..)
    , HasFuncType(..)
    ) where

import           Control.Lens (Prism')
import           Generics.Constraints (makeDerivings, makeInstances)
import           Hyper
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)
import           Text.Show.Combinators ((@|), showCon)

import           Hyper.Internal.Prelude

-- | A term for the types of functions. Analogues to @(->)@ in Haskell.
--
-- @FuncType typ@s express types of functions of @typ@.
--
-- The data type comes along with the 'HasFuncType' class
-- for code to be able to work for any type AST supporting the types of functions.
data FuncType typ h = FuncType
    { _funcIn  :: h :# typ
    , _funcOut :: h :# typ
    } deriving Generic

makeLenses ''FuncType
makeZipMatch ''FuncType
makeHContext ''FuncType
makeHTraversableApplyAndBases ''FuncType
makeDerivings [''Eq, ''Ord] [''FuncType]
makeInstances [''Binary, ''NFData] [''FuncType]

instance Pretty (h :# typ) => Pretty (FuncType typ h) where
    pPrintPrec lvl p (FuncType i o) =
        pPrintPrec lvl 11 i <+> Pretty.text "->" <+> pPrintPrec lvl 10 o
        & maybeParens (p > 10)

instance Show (h :# typ) => Show (FuncType typ h) where
    showsPrec p (FuncType i o) = (showCon "FuncType" @| i @| o) p

-- | HasFuncType is a class of 'HyperType's representing types that support the types of functions.
--
-- It is used by the 'Hyper.Class.Infer.Infer' instances of 'Hyper.Type.AST.App.App' and 'Hyper.Type.AST.Lam.Lam'
-- to work for any AST which provides 'HasFuncType'.
class HasFuncType typ where
    funcType :: Prism' (typ # h) (FuncType typ # h)
