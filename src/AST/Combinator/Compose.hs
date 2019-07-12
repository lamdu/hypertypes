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
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype Compose a b k = MkCompose { getCompose :: Tree a (Compose b (RunKnot k)) }
    deriving Generic

class    ChildrenConstraint k (ComposeConstraint1 c o) => ComposeConstraint0 c k o
instance ChildrenConstraint k (ComposeConstraint1 c o) => ComposeConstraint0 c k o
class    c (Compose k0 k1) => ComposeConstraint1 c k0 k1
instance c (Compose k0 k1) => ComposeConstraint1 c k0 k1

instance (Children k0, Children k1) => Children (Compose k0 k1) where
    type ChildrenConstraint (Compose k0 k1) c = ChildrenConstraint k0 (ComposeConstraint0 c k1)
    children p f x0 =
        _Compose
        (children (p0 p x0)
            (\x1 -> _Compose (children (p1 p x1) (_Compose f)) x1)
        )
        x0
        where
            p0 :: Proxy c -> Tree (Compose k0 k1) n -> Proxy (ComposeConstraint0 c k1)
            p0 _ _ = Proxy
            p1 :: Proxy c -> Tree (Compose k0 n) k1 -> Proxy (ComposeConstraint1 c k1)
            p1 _ _ = Proxy

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
