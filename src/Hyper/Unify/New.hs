-- | Generate new unification variables
{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module Hyper.Unify.New
    ( newUnbound, newTerm, unfreeze
    ) where

import Data.Proxy (Proxy(..))
import Hyper (Tree, Pure)
import Hyper.Class.Unify (Unify(..), UnifyGen(..), UVarOf, BindingDict(..))
import Hyper.Recurse
import Hyper.Unify.Term (UTerm(..), UTermBody(..))

import Prelude.Compat

-- | Create a new unbound unification variable in the current scope
{-# INLINE newUnbound #-}
newUnbound :: forall m t. UnifyGen m t => m (Tree (UVarOf m) t)
newUnbound = scopeConstraints (Proxy @t) >>= newVar binding . UUnbound

-- | Create a new unification term with a given body
{-# INLINE newTerm #-}
newTerm :: forall m t. UnifyGen m t => Tree t (UVarOf m) -> m (Tree (UVarOf m) t)
newTerm x = scopeConstraints (Proxy @t) >>= newVar binding . UTerm . (`UTermBody` x)

-- | Embed a pure term as a unification term
{-# INLINE unfreeze #-}
unfreeze :: forall m t. UnifyGen m t => Tree Pure t -> m (Tree (UVarOf m) t)
unfreeze = wrapM (Proxy @(UnifyGen m) #>> newTerm)
