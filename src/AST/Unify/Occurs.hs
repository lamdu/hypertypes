{-# LANGUAGE NoImplicitPrelude #-}

module AST.Unify.Occurs
    ( occursError
    ) where

import AST (Tree, _Pure)
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Unify.Error (UnifyError(..))
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import AST.Unify.Term (UTerm(..), UTermBody(..))
import Control.Lens.Operators

import Prelude.Compat

occursError ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> m a
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        bindVar binding v (UResolved (_Pure . quantifiedVar # q))
        unifyError (Occurs (quantifiedVar # q) b)
