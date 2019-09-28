{-# LANGUAGE TemplateHaskell, FlexibleContexts, UndecidableInstances #-}

module Hyper.Diff
    ( diff
    , Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), anns, val
    , foldDiffs

    , diffP
    , DiffP(..), _CommonBodyP, _CommonSubTreeP, _DifferentP
    , foldDiffsP
    ) where

import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Hyper
import Hyper.Class.ZipMatch (ZipMatch(..))
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)

import Prelude.Compat

-- | A 'HyperType' which represents the difference between two annotated trees.
-- The annotation types also function as tokens
-- to describe which of the two trees a term comes from.
data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different ((Ann a :*: Ann b) e)
    deriving Generic

-- | A 'HyperType' which represents two trees which have the same top-level node,
-- but their children may differ.
data CommonBody a b e = MkCommonBody
    { _anns :: (a, b)
    , _val :: e # Diff a b
    } deriving Generic

makePrisms ''Diff
makeLenses ''CommonBody

-- | Compute the difference of two annotated trees.
diff ::
    forall t a b.
    (Recursively ZipMatch t, RTraversable t) =>
    Tree (Ann a) t -> Tree (Ann b) t -> Tree (Diff a b) t
diff x@(Ann xA xB) y@(Ann yA yB) =
    withDict (recursively (Proxy @(ZipMatch t))) $
    withDict (recurse (Proxy @(RTraversable t))) $
    case zipMatch xB yB of
    Nothing -> Different (x :*: y)
    Just match ->
        case htraverse (const (^? _CommonSubTree)) sub of
        Nothing -> MkCommonBody (xA, yA) sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub =
                hmap
                ( Proxy @(Recursively ZipMatch) #*# Proxy @RTraversable #>
                    \(xC :*: yC) -> diff xC yC
                ) match

foldDiffs ::
    forall r h a b.
    (Monoid r, Recursively HFoldable h) =>
    (forall n. HRecWitness h n -> Tree (Ann a) n -> Tree (Ann b) n -> r) ->
    Tree (Diff a b) h ->
    r
foldDiffs _ CommonSubTree{} = mempty
foldDiffs f (Different (x :*: y)) = f HRecSelf x y
foldDiffs f (CommonBody (MkCommonBody _ x)) =
    withDict (recursively (Proxy @(HFoldable h))) $
    hfoldMap
    ( Proxy @(Recursively HFoldable) #*#
        \w -> foldDiffs (f . HRecSub w)
    ) x

data DiffP h
    = CommonSubTreeP (HPlain (GetHyperType h))
    | CommonBodyP (h # DiffP)
    | DifferentP (HPlain (GetHyperType h)) (HPlain (GetHyperType h))
    deriving Generic
makePrisms ''DiffP

diffP ::
    forall h.
    (Recursively ZipMatch h, Recursively HasHPlain h, RTraversable h) =>
    HPlain h -> HPlain h -> Tree DiffP h
diffP x y =
    withDict (recursively (Proxy @(HasHPlain h))) $
    diffPH (x ^. hPlain) (y ^. hPlain)

diffPH ::
    forall h.
    (Recursively ZipMatch h, Recursively HasHPlain h, RTraversable h) =>
    Tree Pure h -> Tree Pure h -> Tree DiffP h
diffPH x y =
    withDict (recursively (Proxy @(ZipMatch h))) $
    withDict (recursively (Proxy @(HasHPlain h))) $
    withDict (recurse (Proxy @(RTraversable h))) $
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
                ) match

makeCommonInstances [''Diff, ''CommonBody, ''DiffP]

foldDiffsP ::
    forall r h.
    (Monoid r, Recursively HFoldable h, Recursively HasHPlain h) =>
    (forall n. HasHPlain n => HRecWitness h n -> HPlain n -> HPlain n -> r) ->
    Tree DiffP h ->
    r
foldDiffsP f =
    withDict (recursively (Proxy @(HasHPlain h))) $
    \case
    CommonSubTreeP{} -> mempty
    DifferentP x y -> f HRecSelf x y
    CommonBodyP x ->
        withDict (recursively (Proxy @(HFoldable h))) $
        hfoldMap
        ( Proxy @(Recursively HFoldable) #*# Proxy @(Recursively HasHPlain) #*#
            \w -> foldDiffsP (f . HRecSub w)
        ) x
