{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Hyper.Diff
    ( diff
    , Diff (..)
    , _CommonBody
    , _CommonSubTree
    , _Different
    , CommonBody (..)
    , anns
    , val
    , foldDiffs
    , diffP
    , DiffP (..)
    , _CommonBodyP
    , _CommonSubTreeP
    , _DifferentP
    , foldDiffsP
    ) where

import Hyper
import Hyper.Class.ZipMatch (ZipMatch (..))
import Hyper.Internal.Prelude
import Hyper.Recurse

-- | A 'HyperType' which represents the difference between two annotated trees.
-- The annotation types also function as tokens
-- to describe which of the two trees a term comes from.
data Diff a b e
    = CommonSubTree (Ann (a :*: b) e)
    | CommonBody (CommonBody a b e)
    | Different ((Ann a :*: Ann b) e)
    deriving (Generic)

-- | A 'HyperType' which represents two trees which have the same top-level node,
-- but their children may differ.
data CommonBody a b e = MkCommonBody
    { _anns :: (a :*: b) e
    , _val :: e :# Diff a b
    }
    deriving (Generic)

makePrisms ''Diff
makeLenses ''CommonBody

-- | Compute the difference of two annotated trees.
diff ::
    forall t a b.
    (Recursively ZipMatch t, RTraversable t) =>
    Ann a # t ->
    Ann b # t ->
    Diff a b # t
diff x@(Ann xA xB) y@(Ann yA yB) =
    case zipMatch xB yB of
        Nothing -> Different (x :*: y)
        Just match ->
            case htraverse (const (^? _CommonSubTree)) sub of
                Nothing -> MkCommonBody (xA :*: yA) sub & CommonBody
                Just r -> Ann (xA :*: yA) r & CommonSubTree
            where
                sub =
                    hmap
                        ( Proxy @(Recursively ZipMatch) #*#
                            Proxy @RTraversable #>
                                \(xC :*: yC) -> diff xC yC
                        )
                        match
                        \\ recurse (Proxy @(RTraversable t))
        \\ recursively (Proxy @(ZipMatch t))

foldDiffs ::
    forall r h a b.
    (Monoid r, Recursively HFoldable h) =>
    (forall n. HRecWitness h n -> Ann a # n -> Ann b # n -> r) ->
    Diff a b # h ->
    r
foldDiffs _ CommonSubTree{} = mempty
foldDiffs f (Different (x :*: y)) = f HRecSelf x y
foldDiffs f (CommonBody (MkCommonBody _ x)) =
    hfoldMap
        ( Proxy @(Recursively HFoldable) #*#
            \w -> foldDiffs (f . HRecSub w)
        )
        x
        \\ recursively (Proxy @(HFoldable h))

data DiffP h
    = CommonSubTreeP (HPlain (GetHyperType h))
    | CommonBodyP (h :# DiffP)
    | DifferentP (HPlain (GetHyperType h)) (HPlain (GetHyperType h))
    deriving (Generic)
makePrisms ''DiffP

diffP ::
    forall h.
    (Recursively ZipMatch h, Recursively HasHPlain h, RTraversable h) =>
    HPlain h ->
    HPlain h ->
    DiffP # h
diffP x y =
    diffPH (x ^. hPlain) (y ^. hPlain)
        \\ recursively (Proxy @(HasHPlain h))

diffPH ::
    forall h.
    (Recursively ZipMatch h, Recursively HasHPlain h, RTraversable h) =>
    Pure # h ->
    Pure # h ->
    DiffP # h
diffPH x y =
    case zipMatch (x ^. _Pure) (y ^. _Pure) of
        Nothing -> DifferentP (hPlain # x) (hPlain # y)
        Just match ->
            case htraverse_ (const ((() <$) . (^? _CommonSubTreeP))) sub of
                Nothing -> CommonBodyP sub
                Just () -> _CommonSubTreeP . hPlain # x
            where
                sub =
                    hmap
                        ( Proxy @(Recursively ZipMatch) #*#
                            Proxy @(Recursively HasHPlain) #*#
                                Proxy @RTraversable #>
                                    \(xC :*: yC) -> diffPH xC yC
                        )
                        match
                        \\ recurse (Proxy @(RTraversable h))
        \\ recursively (Proxy @(ZipMatch h))
        \\ recursively (Proxy @(HasHPlain h))

makeCommonInstances [''Diff, ''CommonBody, ''DiffP]

foldDiffsP ::
    forall r h.
    (Monoid r, Recursively HFoldable h, Recursively HasHPlain h) =>
    (forall n. HasHPlain n => HRecWitness h n -> HPlain n -> HPlain n -> r) ->
    DiffP # h ->
    r
foldDiffsP f =
    \case
        CommonSubTreeP{} -> mempty
        DifferentP x y -> f HRecSelf x y
        CommonBodyP x ->
            hfoldMap
                ( Proxy @(Recursively HFoldable) #*#
                    Proxy @(Recursively HasHPlain) #*#
                        \w -> foldDiffsP (f . HRecSub w)
                )
                x
                \\ recursively (Proxy @(HFoldable h))
        \\ recursively (Proxy @(HasHPlain h))
