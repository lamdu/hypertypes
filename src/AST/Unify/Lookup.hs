{-# LANGUAGE NoImplicitPrelude, LambdaCase #-}

module AST.Unify.Lookup
    ( semiPruneLookup
    ) where

import AST
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Unify.Term (UTerm(..))

import Prelude.Compat

-- | Look up a variable, and return last variable pointing to result.
-- Prunes all variables on way to point to the last variable
-- (path-compression ala union-find).
{-# INLINE semiPruneLookup #-}
semiPruneLookup ::
    Unify m t =>
    Tree (UVarOf m) t ->
    m (Tree (UVarOf m) t, Tree (UTerm (UVarOf m)) t)
semiPruneLookup v0 =
    lookupVar binding v0
    >>=
    \case
    UToVar v1 ->
        do
            (v, r) <- semiPruneLookup v1
            bindVar binding v0 (UToVar v)
            pure (v, r)
    t -> pure (v0, t)
