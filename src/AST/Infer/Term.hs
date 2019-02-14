{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, FlexibleInstances #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables, RankNTypes #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , IPayload(..), iplType, iplScope, iplAnn
    , ITerm(..), iVal, iPayload
    , InferChildConstraints
    , iType, iScope, iAnn
    ) where

import AST
import AST.Knot.Flip (Flip(..), _Flip)
import Control.Lens (Lens', makeLenses)
import Control.Lens.Operators
import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data IPayload a v e = IPayload
    { _iplType :: Tree v (TypeOf e)
    , _iplScope :: Tree (ScopeOf e) v
    , _iplAnn :: a
    }

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iVal :: Tie e (ITerm a v)
    , _iPayload :: {-# UNPACK #-} !(IPayload a v (RunKnot e))
    }

makeLenses ''IPayload
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
    children p f (Flip (ITerm b (IPayload t s a))) =
        withDict (recursive :: RecursiveDict (InferChildConstraints c) e) $
        ITerm
        <$> children (Proxy :: Proxy (Recursive (InferChildConstraints c)))
            (fmap (^. _Flip) . children p f . Flip)
            b
        <*> (IPayload
                <$> f t
                <*> children p f s
                <*> pure a
            )
        <&> Flip

iType :: Lens' (ITerm a v e) (Tree v (TypeOf (RunKnot e)))
iType = iPayload . iplType

iScope :: Lens' (ITerm a v e) (Tree (ScopeOf (RunKnot e)) v)
iScope = iPayload . iplScope

iAnn :: Lens' (ITerm a v e) a
iAnn = iPayload . iplAnn
