{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts, DataKinds, ScopedTypeVariables #-}

module AST.Class.Infer
    ( TypeAST, Infer(..), MonadInfer(..)
    , newUnbound, newTerm, unfreeze
    , INode, inferNode, nodeType
    ) where

import           AST.Class.Recursive
import           AST.Knot (Knot, Tree)
import           AST.Knot.Ann (Ann(..), ann)
import           AST.Knot.Pure
import           AST.Unify (Unify(..), UniVar, Binding(..))
import           AST.Unify.Term
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Constraint (withDict)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

type family TypeAST (t :: Knot -> *) :: Knot -> *

type TypeOf m t = Tree (UniVar m) (TypeAST t)
type INode v t a = Tree (Ann (Tree v (TypeAST t), a)) t

class Monad m => MonadInfer m where
    getInferLevel :: m InferLevel
    getInferLevel = pure (InferLevel 0)

    localLevel :: m a -> m a
    -- Default implementation for type systems without skolems
    localLevel = error "Skolems not supported in this type system"

class (Recursive (Unify m) (TypeAST t), MonadInfer m) => Infer m t where
    infer :: Tree t (Ann a) -> m (TypeOf m t, Tree t (Ann (TypeOf m t, a)))

newUnbound :: (MonadInfer m, Unify m t) => m (Tree (UniVar m) t)
newUnbound = getInferLevel >>= newVar binding . UUnbound

newTerm :: (MonadInfer m, Unify m t) => Tree t (UniVar m) -> m (Tree (UniVar m) t)
newTerm x = getInferLevel >>= newVar binding . UTerm . (`UTermBody` x)

-- | Embed a pure term as a mutable term.
unfreeze ::
    forall m t.
    (MonadInfer m, Recursive (Unify m) t) =>
    Tree Pure t -> m (Tree (UniVar m) t)
unfreeze =
    withDict (recursive :: RecursiveDict (Unify m) t) $
    wrapM (Proxy :: Proxy (Unify m)) newTerm

inferNode :: Infer m t => Tree (Ann a) t -> m (INode (UniVar m) t a)
inferNode (Ann a x) =
    infer x <&> \(t, xI) -> Ann (t, a) xI

nodeType :: Lens' (INode v t a) (Tree v (TypeAST t))
nodeType = ann . Lens._1
