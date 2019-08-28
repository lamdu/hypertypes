{-# LANGUAGE TemplateHaskell, FlexibleContexts, UndecidableInstances #-}

module AST.Diff
    ( Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), annPrev, annNew, val
    , diff
    ) where

import AST
import AST.Class.Recursive
import AST.Class.ZipMatch (ZipMatch(..))
import AST.TH.Internal.Instances (makeCommonInstances)
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)

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

makeCommonInstances [''Diff, ''CommonBody]
makePrisms ''Diff
makeLenses ''CommonBody

diff ::
    forall t a b.
    RZipMatchTraversable t =>
    Tree (Ann a) t -> Tree (Ann b) t -> Tree (Diff a b) t
diff x@(Ann xA xB) y@(Ann yA yB) =
    withDict (recursiveZipMatchTraversable (Proxy @t)) $
    case zipMatch xB yB of
    Nothing -> Different (Pair x y)
    Just match ->
        case traverseK (^? _CommonSubTree) sub of
        Nothing -> MkCommonBody xA yA sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub =
                mapKWith (Proxy @RZipMatchTraversable)
                (\(Pair xC yC) -> diff xC yC) match
