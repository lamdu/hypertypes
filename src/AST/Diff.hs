{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, FlexibleContexts #-}

module AST.Diff
    ( diff
    , module AST.Diff.Term
    ) where

import AST
import AST.Class.Recursive (Recursive,  recursiveOverChildren)
import AST.Class.ZipMatch (ZipMatch(..), Both(..))
import AST.Diff.Term
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

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
