{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, DeriveGeneric, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}

module AST.Term.FuncType
    ( FuncType(..), funcIn, funcOut
    , HasFuncType(..)
    ) where

import           AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import           AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import           AST.Knot (Tree, Tie)
import           Control.DeepSeq (NFData)
import           Control.Lens (Prism')
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           GHC.Generics (Generic)

import           Prelude.Compat

data FuncType typ k = FuncType
    { _funcIn  :: Tie k typ
    , _funcOut :: Tie k typ
    } deriving Generic

Lens.makeLenses ''FuncType
makeChildrenAndZipMatch [''FuncType]

instance RecursiveConstraint (FuncType typ) constraint => Recursive constraint (FuncType typ)

deriving instance Eq   (Tie k typ) => Eq   (FuncType typ k)
deriving instance Ord  (Tie k typ) => Ord  (FuncType typ k)
instance Binary (Tie k typ) => Binary (FuncType typ k)
instance NFData (Tie k typ) => NFData (FuncType typ k)

instance Show (Tie k typ) => Show (FuncType typ k) where
    showsPrec p (FuncType i o) =
        showParen (p > 10) (("FuncType " <>) . showsPrec 11 i . (" " <>) . showsPrec 11 o)

class HasFuncType typ where
    funcType :: Prism' (Tree typ k) (Tree (FuncType typ) k)
