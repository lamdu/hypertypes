{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, FlexibleContexts, DefaultSignatures #-}

module AST.Class.Instantiate where

import           AST.Class.Children
import           AST.Class.Recursive
import           AST.Knot
import           AST.Knot.Pure
import           AST.Unify

class Children scheme => Instantiate scheme where
    type family SchemeType scheme :: Knot -> *
    type SchemeType scheme = scheme

    instantiate ::
        Recursive (Unify m) (SchemeType scheme) =>
        Tree Pure scheme -> m (Tree (UniVar m) (SchemeType scheme))
    default instantiate ::
        (SchemeType scheme ~ scheme, Recursive (Unify m) (SchemeType scheme)) =>
        Tree Pure scheme -> m (Tree (UniVar m) (SchemeType scheme))
    instantiate = unfreeze
