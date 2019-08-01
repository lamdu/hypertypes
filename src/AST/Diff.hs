{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts, ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving, UndecidableInstances, KindSignatures, DeriveGeneric #-}
{-# LANGUAGE DataKinds, ScopedTypeVariables #-}

module AST.Diff
    ( Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), annPrev, annNew, val
    , diff
    ) where

import AST
import AST.Class.Recursive (Recursively)
import AST.Class.ZipMatch (ZipMatch(..))
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (Constraint, withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Text.Show.Combinators

import Prelude.Compat

-- | Diff of two annotated ASTs.
-- The annotation types also function as tokens to describe which of the two ASTs a term comes from.

data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different (Product (Ann a) (Ann b) e)
    deriving Generic

data CommonBody a b e = MkCommonBody
    { _annPrev :: a
    , _annNew :: b
    , _val :: Node e (Diff a b)
    } deriving Generic

makePrisms ''Diff
makeLenses ''CommonBody

diff ::
    forall t a b.
    (Recursively ZipMatch t, Recursively KTraversable t) =>
    Tree (Ann a) t -> Tree (Ann b) t -> Tree (Diff a b) t
diff x@(Ann xA xB) y@(Ann yA yB) =
    withDict (recursive :: RecursiveDict t ZipMatch) $
    withDict (recursive :: RecursiveDict t KTraversable) $
    case zipMatch xB yB of
    Nothing -> Different (Pair x y)
    Just match ->
        case traverseK (^? _CommonSubTree) sub of
        Nothing -> MkCommonBody xA yA sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub =
                mapKWith (Proxy :: Proxy '[Recursively ZipMatch, Recursively KTraversable])
                (\(Pair xC yC) -> diff xC yC) match

type Deps c a b e =
    (
        ( c a, c b
        , c (Node e (Ann a)), c (Node e (Ann b))
        , c (Node e (Ann (a, b)))
        , c (Node e (Diff a b))
        ) :: Constraint
    )
deriving instance Deps Eq   a b e => Eq   (CommonBody a b e)
deriving instance Deps Eq   a b e => Eq   (Diff a b e)
deriving instance Deps Ord  a b e => Ord  (CommonBody a b e)
deriving instance Deps Ord  a b e => Ord  (Diff a b e)
deriving instance Deps Show a b e => Show (CommonBody a b e)
deriving instance Deps Show a b e => Show (Diff a b e)
