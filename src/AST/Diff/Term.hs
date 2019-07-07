{-# LANGUAGE NoImplicitPrelude, TemplateHaskell #-}

module AST.Diff.Term
    ( Diff(..), _CommonBody, _CommonSubTree, _Different
    , CommonBody(..), annPrev, annNew, val
    ) where

import AST (Ann, Tie)
import AST.Knot.Both (Both)
import Control.Lens (makeLenses, makePrisms)

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
