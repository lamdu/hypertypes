{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, FlexibleContexts, DefaultSignatures, ConstraintKinds #-}

module AST.Class.Instantiate
    ( Instantiate(..)
    ) where

import AST.Class.Children
import AST.Class.Infer
import AST.Class.Recursive
import AST.Knot
import AST.Knot.Pure
import AST.Unify
import Data.Constraint (Constraint)

type DefaultInstantiateContext scheme m =
    ( MonadInfer m
    , Recursive (Unify m) (SchemeType scheme)
    )

class Children scheme => Instantiate scheme where
    type family SchemeType scheme :: Knot -> *
    type SchemeType scheme = scheme

    type family InstantiateContext scheme (m :: * -> *) :: Constraint
    type instance InstantiateContext scheme m = DefaultInstantiateContext scheme m

    instantiate ::
        InstantiateContext scheme m =>
        Tree Pure scheme -> m (Tree (UniVar m) (SchemeType scheme))
    default instantiate ::
        ( SchemeType scheme ~ scheme
        , InstantiateContext scheme m ~ DefaultInstantiateContext scheme m
        , InstantiateContext scheme m
        ) =>
        Tree Pure scheme -> m (Tree (UniVar m) (SchemeType scheme))
    instantiate = unfreeze
