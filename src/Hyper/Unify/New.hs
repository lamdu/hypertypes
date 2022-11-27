{-# LANGUAGE FlexibleContexts #-}

-- | Generate new unification variables
module Hyper.Unify.New
    ( newUnbound
    , newTerm
    , unfreeze
    ) where

import Hyper
import Hyper.Class.Unify (BindingDict (..), UVarOf, Unify (..), UnifyGen (..))
import Hyper.Recurse
import Hyper.Unify.Term (UTerm (..), UTermBody (..))

import Prelude.Compat

-- | Create a new unbound unification variable in the current scope
{-# INLINE newUnbound #-}
newUnbound :: forall m t. UnifyGen m t => m (UVarOf m # t)
newUnbound = scopeConstraints (Proxy @t) >>= newVar binding . UUnbound

-- | Create a new unification term with a given body
{-# INLINE newTerm #-}
newTerm :: forall m t. UnifyGen m t => t # UVarOf m -> m (UVarOf m # t)
newTerm x = scopeConstraints (Proxy @t) >>= newVar binding . UTerm . (`UTermBody` x)

-- | Embed a pure term as a unification term
{-# INLINE unfreeze #-}
unfreeze :: forall m t. UnifyGen m t => Pure # t -> m (UVarOf m # t)
unfreeze = wrapM (Proxy @(UnifyGen m) #>> newTerm)
