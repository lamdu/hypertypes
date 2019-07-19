{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric, TemplateHaskell, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module AST.Term.FuncType
    ( FuncType(..), funcIn, funcOut
    , HasFuncType(..)
    ) where

import           AST
import           AST.Combinator.Single (Single)
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
    { _funcIn  :: Tie k typ
    , _funcOut :: Tie k typ
    } deriving Generic

type instance ChildrenTypesOf (FuncType t) = Single t

makeLenses ''FuncType
makeChildrenAndZipMatch ''FuncType
makeKApplicativeAndBases ''FuncType
makeKTraversableAndFoldable ''FuncType

instance Pretty (Tie k typ) => Pretty (FuncType typ k) where
    pPrintPrec lvl p (FuncType i o) =
        pPrintPrec lvl 11 i <+> Pretty.text "->" <+> pPrintPrec lvl 10 o
        & maybeParens (p > 10)

instance RecursiveConstraint (FuncType typ) constraint => Recursive constraint (FuncType typ)

instance Show (Tie k typ) => Show (FuncType typ k) where
    showsPrec p (FuncType i o) = (showCon "FuncType" @| i @| o) p

class HasFuncType typ where
    funcType :: Prism' (Tree typ k) (Tree (FuncType typ) k)

deriving instance Eq  (Tie k typ) => Eq  (FuncType typ k)
deriving instance Ord (Tie k typ) => Ord (FuncType typ k)
instance Binary (Tie k typ) => Binary (FuncType typ k)
instance NFData (Tie k typ) => NFData (FuncType typ k)
