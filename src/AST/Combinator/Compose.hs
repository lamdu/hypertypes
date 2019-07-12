{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, DeriveGeneric #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module AST.Combinator.Compose
    ( Compose(..)
    ) where

import           AST
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype Compose a b k = MkCompose { getCompose :: Tree a (Compose b (RunKnot k)) }
    deriving Generic

{-# INLINE _Compose #-}
_Compose ::
    Lens.Iso
    (Tree (Compose a0 b0) k0) (Tree (Compose a1 b1) k1)
    (Tree a0 (Compose b0 k0)) (Tree a1 (Compose b1 k1))
_Compose = Lens.iso getCompose MkCompose

type InCompose a b k = Tree a (Compose b (RunKnot k))
deriving instance Eq   (InCompose a b k) => Eq   (Compose a b k)
deriving instance Ord  (InCompose a b k) => Ord  (Compose a b k)
deriving instance Show (InCompose a b k) => Show (Compose a b k)
instance Binary (InCompose a b k) => Binary (Compose a b k)
instance NFData (InCompose a b k) => NFData (Compose a b k)
