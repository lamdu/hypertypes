{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , IPayload(..), iplType, iplScope, iplAnn
    , ITerm(..), iVal, iPayload
    , iType, iScope, iAnn
    ) where

import AST
import Control.Lens (Lens', makeLenses)

import Prelude.Compat

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

data IPayload a v e = IPayload
    { _iplType :: Tree v (TypeOf (RunKnot e))
    , _iplScope :: Tree (ScopeOf (RunKnot e)) v
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
    , _iPayload :: {-# UNPACK #-} !(IPayload a v e)
    }

makeLenses ''IPayload
makeLenses ''ITerm

iType :: Lens' (ITerm a v e) (Tree v (TypeOf (RunKnot e)))
iType = iPayload . iplType

iScope :: Lens' (ITerm a v e) (Tree (ScopeOf (RunKnot e)) v)
iScope = iPayload . iplScope

iAnn :: Lens' (ITerm a v e) a
iAnn = iPayload . iplAnn
