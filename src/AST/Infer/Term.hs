{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables, RankNTypes, StandaloneDeriving #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , IResult(..), irType, irScope
    , ITerm(..), iVal, iRes, iAnn
    , InferChildConstraints, InferChildDeps
    , iType, iScope, iAnnotations
    ) where

import AST
import AST.Class.Functor
import AST.Combinator.Both
import AST.Combinator.Flip (Flip(..), _Flip)
import Control.Lens (Traversal, Lens', makeLenses, from)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy (Proxy(..))

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data IResult e v = IResult
    { _irType :: Tie v (TypeOf e)
    , _irScope :: ScopeOf e v
    }
makeLenses ''IResult

data IResultChildrenTypes e k = IResultChildrenTypes
    { _ircType :: Tie k (TypeOf e)
    , _ircScope :: ChildrenTypesOf (ScopeOf e) k
    }

type instance ChildrenTypesOf (IResult e) = IResultChildrenTypes e
type instance ChildrenTypesOf (IResultChildrenTypes e) = IResultChildrenTypes e

makeKPointed ''IResultChildrenTypes

instance
    HasChildrenTypes (ScopeOf e) =>
    HasChildrenTypes (IResultChildrenTypes e) where

    {-# INLINE hasChildrenTypes #-}
    hasChildrenTypes _ =
        withDict (hasChildrenTypes (Proxy :: Proxy (ScopeOf e))) Dict

instance
    HasChildrenTypes (ScopeOf e) =>
    KFunctor (IResultChildrenTypes e) where

    {-# INLINE mapC #-}
    mapC (IResultChildrenTypes (MkMapK mapType) mapScope) (IResultChildrenTypes t s) =
        IResultChildrenTypes
        { _ircType = mapType t
        , _ircScope =
            withDict (hasChildrenTypes (Proxy :: Proxy (ScopeOf e))) $
            mapC mapScope s
        }

instance
    HasChildrenTypes (ScopeOf e) =>
    KApply (IResultChildrenTypes e) where

    {-# INLINE zipK #-}
    zipK (IResultChildrenTypes t0 s0) (IResultChildrenTypes t1 s1) =
        withDict (hasChildrenTypes (Proxy :: Proxy (ScopeOf e))) $
        IResultChildrenTypes (Both t0 t1) (zipK s0 s1)

instance
    HasChildrenTypes (ScopeOf e) =>
    HasChildrenTypes (IResult e) where

    {-# INLINE hasChildrenTypes #-}
    hasChildrenTypes _ =
        withDict (hasChildrenTypes (Proxy :: Proxy (ScopeOf e))) Dict

makeKApplicativeBases ''IResult
makeKTraversableAndFoldable ''IResult

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iAnn :: a
    , _iRes :: {-# UNPACK #-} !(Tree (IResult (RunKnot e)) v)
    , _iVal :: Tie e (ITerm a v)
    }
makeLenses ''ITerm

type InferChildDeps c ast =
    ( c (TypeOf ast)
    , KTraversable ast
    , KLiftConstraint (ChildrenTypesOf (ScopeOf ast)) c
    , ChildrenWithConstraint (ScopeOf ast) c
    )
class    InferChildDeps c ast => InferChildConstraints c ast
instance InferChildDeps c ast => InferChildConstraints c ast

instance Children (Flip (ITerm a) e) where
    type ChildrenConstraint (Flip (ITerm a) e) c = Recursive (InferChildConstraints c) e
    {-# INLINE children #-}
    children ::
        forall f c n m.
        (Applicative f, Recursive (InferChildConstraints c) e) =>
        Proxy c ->
        (forall child. c child => Tree n child -> f (Tree m child)) ->
        Tree (Flip (ITerm a) e) n -> f (Tree (Flip (ITerm a) e) m)
    children p f (MkFlip (ITerm a (IResult t s) b)) =
        ITerm a
        <$> (IResult <$> f t <*> children p f s)
        <*> recursiveChildren (Proxy :: Proxy (InferChildConstraints c))
            (from _Flip (children p f)) b
        <&> (_Flip #)

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

deriving instance (Show (Tree v (TypeOf e)), Show (Tree (ScopeOf e) v)) => Show (Tree (IResult e) v)
deriving instance (Show a, Show (Tie e (ITerm a v)), Show (Tree (IResult (RunKnot e)) v)) => Show (ITerm a v e)
