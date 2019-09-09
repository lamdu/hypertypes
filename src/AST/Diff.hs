{-# LANGUAGE TemplateHaskell, FlexibleContexts, UndecidableInstances #-}

module AST.Diff
    ( diff
    , Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), anns, val
    ) where

import AST
import AST.Class.ZipMatch (ZipMatch(..))
import AST.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | A 'Knot' which represents the difference between two annotated trees.
-- The annotation types also function as tokens
-- to describe which of the two trees a term comes from.
data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different (Product (Ann a) (Ann b) e)
    deriving Generic

-- | A 'Knot' which represents two trees which have the same top-level node,
-- but their children may differ.
data CommonBody a b e = MkCommonBody
    { _anns :: (a, b)
    , _val :: e # Diff a b
    } deriving Generic

makeCommonInstances [''Diff, ''CommonBody]
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
