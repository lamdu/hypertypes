{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyper.Syntax.FuncType
    ( FuncType (..)
    , funcIn
    , funcOut
    , W_FuncType (..)
    , MorphWitness (..)
    ) where

import Generics.Constraints (makeDerivings, makeInstances)
import Hyper
import Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import Text.PrettyPrint.HughesPJClass (Pretty (..), maybeParens)
import Text.Show.Combinators (showCon, (@|))

import Hyper.Internal.Prelude

-- | A term for the types of functions. Analogues to @(->)@ in Haskell.
--
-- @FuncType typ@s express types of functions of @typ@.
data FuncType typ h = FuncType
    { _funcIn :: h :# typ
    , _funcOut :: h :# typ
    }
    deriving (Generic)

makeLenses ''FuncType
makeZipMatch ''FuncType
makeHContext ''FuncType
makeHMorph ''FuncType
makeHTraversableApplyAndBases ''FuncType
makeDerivings [''Eq, ''Ord] [''FuncType]
makeInstances [''Binary, ''NFData] [''FuncType]

instance Pretty (h :# typ) => Pretty (FuncType typ h) where
    pPrintPrec lvl p (FuncType i o) =
        pPrintPrec lvl 11 i <+> Pretty.text "->" <+> pPrintPrec lvl 10 o
            & maybeParens (p > 10)

instance Show (h :# typ) => Show (FuncType typ h) where
    showsPrec p (FuncType i o) = (showCon "FuncType" @| i @| o) p
