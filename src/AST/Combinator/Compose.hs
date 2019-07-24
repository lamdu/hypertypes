{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, DeriveGeneric #-}
{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances, DerivingStrategies, ScopedTypeVariables #-}

module AST.Combinator.Compose
    ( Compose(..), _Compose
    ) where

import           AST
import           AST.Class.Apply
import           AST.Class.Foldable
import           AST.Class.Functor
import           AST.Class.Traversable
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

instance
    (HasChildrenTypes a, KPointed a, KPointed b) =>
    KPointed (Compose a b) where
    type KLiftConstraint (Compose a b) c = KLiftConstraint a (ComposeConstraint0K c b)
    {-# INLINE pureC #-}
    pureC =
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        _Compose %~ pureC . mapK (_Compose %~ pureC)
    {-# INLINE pureK #-}
    pureK x = pureK (pureK (MkCompose x) & MkCompose) & MkCompose
    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p x =
        pureKWithConstraint (p0 p) (makeP1 p (\p1 -> pureKWithConstraint p1 (MkCompose x) & MkCompose))
        & MkCompose
        where
            p0 :: Proxy c -> Proxy (ComposeConstraint0K c b)
            p0 _ = Proxy
            makeP1 ::
                Proxy c ->
                (Proxy (ComposeConstraint1 c k1) -> Tree k0 k1) ->
                Tree k0 k1
            makeP1 = undefined

instance
    (HasChildrenTypes a, HasChildrenTypes b, KFunctor a, KFunctor b) =>
    KFunctor (Compose a b) where
    {-# INLINE mapC #-}
    mapC (MkCompose f) =
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        withDict (hasChildrenTypes (Proxy :: Proxy b)) $
        _Compose %~
        mapC
        ( mapK
            ( \(MkCompose bT) ->
                MkMapK (_Compose %~ mapC (mapK ((_MapK %~ (_Compose %~)) . getCompose) bT))
            ) f
        )

instance
    (HasChildrenTypes a, HasChildrenTypes b, KApply a, KApply b) =>
    KApply (Compose a b) where
    {-# INLINE zipK #-}
    zipK (MkCompose a0) =
        _Compose %~
        mapK
            ( \(Both (MkCompose b0) (MkCompose b1)) ->
                zipK b0 b1
                & mapK
                    ( \(Both (MkCompose i0) (MkCompose i1)) ->
                        Both i0 i1 & MkCompose
                    )
                & MkCompose
            )
        . zipK a0

instance
    (HasChildrenTypes a, HasChildrenTypes b, KFoldable a, KFoldable b) =>
    KFoldable (Compose a b) where
    {-# INLINE foldMapC #-}
    foldMapC (MkCompose f) =
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        withDict (hasChildrenTypes (Proxy :: Proxy b)) $
        foldMapC
        ( mapK
            ( \(MkCompose bf) ->
                MkConvertK
                ( foldMapC
                    ( mapK ((_ConvertK %~ (. getCompose)) . getCompose) bf
                    ) . getCompose
                )
            ) f
        ) . getCompose

instance
    (HasChildrenTypes a, HasChildrenTypes b, KTraversable a, KTraversable b) =>
    KTraversable (Compose a b) where
    {-# INLINE sequenceC #-}
    sequenceC =
        _Compose
        ( sequenceC .
            mapK (MkContainedK . _Compose (traverseK (_Compose runContainedK)))
        )

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
    , HasChildrenTypes k0, HasChildrenTypes k1, KTraversable k0, KFunctor k1
    ) =>
    ZipMatch (Compose k0 k1) where
    {-# INLINE zipMatch #-}
    zipMatch (MkCompose x) (MkCompose y) =
        zipMatch x y
        >>= traverseK
            (\(Both (MkCompose cx) (MkCompose cy)) ->
                zipMatch cx cy
                <&> mapK
                    (\(Both (MkCompose bx) (MkCompose by)) -> Both bx by & MkCompose)
                <&> MkCompose
            )
        <&> MkCompose

type InCompose a b k = Tree a (Compose b (RunKnot k))
deriving instance Eq   (InCompose a b k) => Eq   (Compose a b k)
deriving instance Ord  (InCompose a b k) => Ord  (Compose a b k)
deriving instance Show (InCompose a b k) => Show (Compose a b k)
instance Binary (InCompose a b k) => Binary (Compose a b k)
instance NFData (InCompose a b k) => NFData (Compose a b k)
