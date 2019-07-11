{-# LANGUAGE NoImplicitPrelude #-}

module AST.Unify.Occurs
    ( occursError
    ) where

import AST (Tree, Pure, _Pure)
import AST.Class.Unify (Unify(..), UVarOf, BindingDict(..))
import AST.Unify.Error (UnifyError(..))
import AST.Unify.QuantifiedVar (HasQuantifiedVar(..), MonadQuantify(..))
import AST.Unify.Term (UTerm(..), UTermBody(..))
import Control.Lens.Operators

import Prelude.Compat

occursError ::
    Unify m t =>
    Tree (UVarOf m) t -> Tree (UTermBody (UVarOf m)) t -> m (Tree Pure t)
occursError v (UTermBody c b) =
    do
        q <- newQuantifiedVariable c
        let r = quantifiedVar # q
        bindVar binding v (UResolved (_Pure # r))
        _Pure # r <$ unifyError (Occurs (quantifiedVar # q) b)
