{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, DeriveGeneric #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances, DerivingStrategies, ScopedTypeVariables #-}

module AST.Combinator.Compose
    ( Compose(..)
    ) where

import           AST
import           AST.Class.HasChildrenTypes
import           AST.Class.Combinators (NoConstraint)
import           AST.Class.Pointed
import           AST.Class.ZipMatch (ZipMatch(..), Both(..))
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)

import           Prelude.Compat

newtype Compose a b k = MkCompose { getCompose :: Tree a (Compose b (RunKnot k)) }
    deriving stock Generic

{-# INLINE _Compose #-}
_Compose ::
    Lens.Iso
    (Tree (Compose a0 b0) k0) (Tree (Compose a1 b1) k1)
    (Tree a0 (Compose b0 k0)) (Tree a1 (Compose b1 k1))
_Compose = Lens.iso getCompose MkCompose

type instance ChildrenTypesOf (Compose a b) = Compose (ChildrenTypesOf a) (ChildrenTypesOf b)

-- TODO: Remove ComposeConstraint0 when get rid of Children class
class    ChildrenConstraint k (ComposeConstraint1 c o) => ComposeConstraint0 c k o
instance ChildrenConstraint k (ComposeConstraint1 c o) => ComposeConstraint0 c k o

class    KLiftConstraint k (ComposeConstraint1 c o) => ComposeConstraint0K c k o
instance KLiftConstraint k (ComposeConstraint1 c o) => ComposeConstraint0K c k o
class    c (Compose k0 k1) => ComposeConstraint1 c k0 k1
instance c (Compose k0 k1) => ComposeConstraint1 c k0 k1

instance (HasChildrenTypes a, KPointed a, KPointed b) => KPointed (Compose a b) where
    type KLiftConstraint (Compose a b) c = KLiftConstraint a (ComposeConstraint0K c b)
    pureC =
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        withDict (hasChildrenTypes (Proxy :: Proxy (ChildrenTypesOf a))) $
        _Compose %~ pureC . mapK (_Compose %~ pureC)
    pureK x = pureK (pureK (MkCompose x) & MkCompose) & MkCompose
    pureKWith p x =
        pureKWith (p0 p) (makeP1 p (\p1 -> pureKWith p1 (MkCompose x) & MkCompose)) & MkCompose
        where
            p0 :: Proxy c -> Proxy (ComposeConstraint0K c b)
            p0 _ = Proxy
            makeP1 ::
                Proxy c ->
                (Proxy (ComposeConstraint1 c k1) -> Tree k0 k1) ->
                Tree k0 k1
            makeP1 = undefined

instance (Children k0, Children k1) => Children (Compose k0 k1) where
    type ChildrenConstraint (Compose k0 k1) c = ChildrenConstraint k0 (ComposeConstraint0 c k1)
    children p f =
        _Compose
        (children (p0 p)
            (\x1 -> _Compose (children (p1 p x1) (_Compose f)) x1)
        )
        where
            p0 :: Proxy c -> Proxy (ComposeConstraint0 c k1)
            p0 _ = Proxy
            p1 :: Proxy c -> Tree (Compose a n) b -> Proxy (ComposeConstraint1 c b)
            p1 _ _ = Proxy

instance
    ( ZipMatch k0, ZipMatch k1
    , ChildrenConstraint k0 NoConstraint
    , ChildrenConstraint k1 NoConstraint
    ) =>
    ZipMatch (Compose k0 k1) where
    zipMatch (MkCompose x) (MkCompose y) =
        zipMatch x y
        >>= children p
            (\(Both (MkCompose cx) (MkCompose cy)) ->
                zipMatch cx cy
                <&> overChildren p
                    (\(Both (MkCompose bx) (MkCompose by)) -> Both bx by & MkCompose)
                <&> MkCompose
            )
        <&> MkCompose
        where
            p :: Proxy NoConstraint
            p = Proxy

type InCompose a b k = Tree a (Compose b (RunKnot k))
deriving instance Eq   (InCompose a b k) => Eq   (Compose a b k)
deriving instance Ord  (InCompose a b k) => Ord  (Compose a b k)
deriving instance Show (InCompose a b k) => Show (Compose a b k)
instance Binary (InCompose a b k) => Binary (Compose a b k)
instance NFData (InCompose a b k) => NFData (Compose a b k)
