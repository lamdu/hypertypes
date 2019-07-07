{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts #-}

module AST.Diff
    ( Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), annPrev, annNew, val
    , diff
    ) where

import AST
import AST.Class.Recursive (Recursive,  recursiveOverChildren)
import AST.Class.ZipMatch (ZipMatch(..), Both(..))
import Control.Lens (makeLenses, makePrisms)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | Diff of two annotated ASTs.
-- The annotation types also function as tokens to describe which of the two ASTs a term comes from.

data Diff a b e
    = CommonSubTree (Ann (a, b) e)
    | CommonBody (CommonBody a b e)
    | Different (Both (Ann a) (Ann b) e)

data CommonBody a b e = MkCommonBody
    { _annPrev :: a
    , _annNew :: b
    , _val :: Tie e (Diff a b)
    }

makePrisms ''Diff
makeLenses ''CommonBody

diff ::
    Recursive ZipMatch t =>
    Tree (Ann a) t -> Tree (Ann b) t -> Tree (Diff a b) t
diff x@(Ann xA xB) y@(Ann yA yB) =
    case zipMatch xB yB of
    Nothing -> Different (Both x y)
    Just match ->
        case recursiveChildren (Proxy :: Proxy ZipMatch) (^? _CommonSubTree) sub of
        Nothing -> MkCommonBody xA yA sub & CommonBody
        Just r -> Ann (xA, yA) r & CommonSubTree
        where
            sub = recursiveOverChildren (Proxy :: Proxy ZipMatch) (\(Both xC yC) -> diff xC yC) match
