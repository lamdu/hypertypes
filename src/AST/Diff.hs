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
import AST.Class.ZipMatch (ZipMatch(..), Both(..))
import Control.DeepSeq (NFData)
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Constraint (Constraint, withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

import Prelude.Compat

-- | Diff of two annotated ASTs.
-- The annotation types also function as tokens to describe which of the two ASTs a term comes from.

data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different (Both (Ann a) (Ann b) e)
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
    Recursively ZipMatch t =>
    Tree (Ann a) t -> Tree (Ann b) t -> Tree (Diff a b) t
diff x@(Ann xA xB) y@(Ann yA yB) =
    withDict (recursive :: RecursiveDict t ZipMatch) $
    case zipMatch xB yB of
    Nothing -> Different (Both x y)
    Just match ->
        case traverseK (^? _CommonSubTree) sub of
        Nothing -> MkCommonBody xA yA sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub =
                mapKWith (Proxy :: Proxy '[Recursively ZipMatch]) (\(Both xC yC) -> diff xC yC) match

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
instance Deps Binary a b e => Binary (CommonBody a b e)
instance Deps Binary a b e => Binary (Diff a b e)
instance Deps NFData a b e => NFData (CommonBody a b e)
instance Deps NFData a b e => NFData (Diff a b e)
