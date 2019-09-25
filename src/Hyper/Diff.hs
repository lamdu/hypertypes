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

import Hyper
import Hyper.Class.ZipMatch (ZipMatch(..))
import Hyper.Recurse
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | A 'AHyperType' which represents the difference between two annotated trees.
-- The annotation types also function as tokens
-- to describe which of the two trees a term comes from.
data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different (Product (Ann a) (Ann b) e)
    deriving Generic

-- | A 'AHyperType' which represents two trees which have the same top-level node,
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
    Nothing -> Different (Pair x y)
    Just match ->
        case traverseK (const (^? _CommonSubTree)) sub of
        Nothing -> MkCommonBody (xA, yA) sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub =
                mapK
                ( Proxy @(Recursively ZipMatch) #*# Proxy @RTraversable #>
                    \(Pair xC yC) -> diff xC yC
                ) match

foldDiffs ::
    forall r k a b.
    (Monoid r, Recursively HFoldable k) =>
    (forall n. HRecWitness k n -> Tree (Ann a) n -> Tree (Ann b) n -> r) ->
    Tree (Diff a b) k ->
    r
foldDiffs _ CommonSubTree{} = mempty
foldDiffs f (Different (Pair x y)) = f HRecSelf x y
foldDiffs f (CommonBody (MkCommonBody _ x)) =
    withDict (recursively (Proxy @(HFoldable k))) $
    foldMapK
    ( Proxy @(Recursively HFoldable) #*#
        \w -> foldDiffs (f . HRecSub w)
    ) x

data DiffP k
    = CommonSubTreeP (HPlain (GetHyperType k))
    | CommonBodyP (k # DiffP)
    | DifferentP (HPlain (GetHyperType k)) (HPlain (GetHyperType k))
    deriving Generic
makePrisms ''DiffP

diffP ::
    forall k.
    (Recursively ZipMatch k, Recursively HasHPlain k, RTraversable k) =>
    HPlain k -> HPlain k -> Tree DiffP k
diffP x y =
    withDict (recursively (Proxy @(HasHPlain k))) $
    diffPH (x ^. kPlain) (y ^. kPlain)

diffPH ::
    forall k.
    (Recursively ZipMatch k, Recursively HasHPlain k, RTraversable k) =>
    Tree Pure k -> Tree Pure k -> Tree DiffP k
diffPH x y =
    withDict (recursively (Proxy @(ZipMatch k))) $
    withDict (recursively (Proxy @(HasHPlain k))) $
    withDict (recurse (Proxy @(RTraversable k))) $
    case zipMatch (x ^. _Pure) (y ^. _Pure) of
    Nothing -> DifferentP (kPlain # x) (kPlain # y)
    Just match ->
        case traverseK_ (const ((() <$) . (^? _CommonSubTreeP))) sub of
        Nothing -> CommonBodyP sub
        Just () -> _CommonSubTreeP . kPlain # x
        where
            sub =
                mapK
                ( Proxy @(Recursively ZipMatch) #*#
                    Proxy @(Recursively HasHPlain) #*#
                    Proxy @RTraversable #>
                    \(Pair xC yC) -> diffPH xC yC
                ) match

makeCommonInstances [''Diff, ''CommonBody, ''DiffP]

foldDiffsP ::
    forall r k.
    (Monoid r, Recursively HFoldable k, Recursively HasHPlain k) =>
    (forall n. HasHPlain n => HRecWitness k n -> HPlain n -> HPlain n -> r) ->
    Tree DiffP k ->
    r
foldDiffsP f =
    withDict (recursively (Proxy @(HasHPlain k))) $
    \case
    CommonSubTreeP{} -> mempty
    DifferentP x y -> f HRecSelf x y
    CommonBodyP x ->
        withDict (recursively (Proxy @(HFoldable k))) $
        foldMapK
        ( Proxy @(Recursively HFoldable) #*# Proxy @(Recursively HasHPlain) #*#
            \w -> foldDiffsP (f . HRecSub w)
        ) x
