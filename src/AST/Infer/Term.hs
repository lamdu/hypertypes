{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables, RankNTypes, StandaloneDeriving #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , IResult(..), irType, irScope
    , ITerm(..), iVal, iRes, iAnn
    , InferChildConstraints
    , iType, iScope, iAnnotations
    ) where

import AST
import AST.Knot.Flip (Flip(..), _Flip)
import Control.Lens (Traversal, Lens', makeLenses, from)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data IResult v e = IResult
    { _irType :: Tree v (TypeOf e)
    , _irScope :: Tree (ScopeOf e) v
    }
makeLenses ''IResult

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: {-# UNPACK #-} !(IResult v (RunKnot e))
    , _iVal :: Tie e (ITerm a v)
    }
makeLenses ''ITerm

class    (c (TypeOf ast), ChildrenWithConstraint (ScopeOf ast) c) => InferChildConstraints c ast
instance (c (TypeOf ast), ChildrenWithConstraint (ScopeOf ast) c) => InferChildConstraints c ast

instance Children (Flip (ITerm a) e) where
    type ChildrenConstraint (Flip (ITerm a) e) c = Recursive (InferChildConstraints c) e
    {-# INLINE children #-}
    children ::
        forall f c n m.
        (Applicative f, Recursive (InferChildConstraints c) e) =>
        Proxy c ->
        (forall child. c child => Tree n child -> f (Tree m child)) ->
        Tree (Flip (ITerm a) e) n -> f (Tree (Flip (ITerm a) e) m)
    children p f (Flip (ITerm a (IResult t s) b)) =
        ITerm a
        <$> (IResult <$> f t <*> children p f s)
        <*> recursiveChildren (Proxy :: Proxy (InferChildConstraints c))
            (from _Flip (children p f)) b
        <&> Flip

iType :: Lens' (ITerm a v e) (Tree v (TypeOf (RunKnot e)))
iType = iRes . irType

iScope :: Lens' (ITerm a v e) (Tree (ScopeOf (RunKnot e)) v)
iScope = iRes . irScope

iAnnotations ::
    Recursive Children e =>
    Traversal
    (Tree (ITerm a v) e)
    (Tree (ITerm b v) e)
    a b
iAnnotations f (ITerm pl r x) =
    ITerm
    <$> f pl
    <*> pure r
    <*> recursiveChildren (Proxy :: Proxy Children) (iAnnotations f) x

deriving instance (Show (Tree v (TypeOf e)), Show (Tree (ScopeOf e) v)) => Show (IResult v e)
deriving instance (Show a, Show (Tie e (ITerm a v)), Show (IResult v (RunKnot e))) => Show (ITerm a v e)
