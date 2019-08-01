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
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Binary (Binary)
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

-- Note on manual instances below -
-- `Data.Functor.Product` only has `Eq` instances when it is a product of functors
-- which have `Eq1` instances, however unfortunately `Eq1` is not poly-kinded,
-- so we can't declare an `Eq1` instance for `Ann` and other knots.

instance Deps Show a b e => Show (Diff a b e) where
    showsPrec p b =
        p &
        case b of
        CommonSubTree x -> showCon "CommonSubTree" @| x
        CommonBody x -> showCon "CommonBody" @| x
        Different (Pair x y) ->
            -- Work around missing instance for `Data.Functor.Product`
            showCon "Different" `showApp` (showCon "Pair" @| x @| y)

deriving instance Deps Eq   a b e => Eq   (CommonBody a b e)
deriving instance Deps Ord  a b e => Ord  (CommonBody a b e)
deriving instance Deps Show a b e => Show (CommonBody a b e)
instance Deps Binary a b e => Binary (CommonBody a b e)
instance Deps NFData a b e => NFData (CommonBody a b e)
