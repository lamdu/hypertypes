{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, TypeFamilies #-}

module AST.Infer.Term
    ( TypeOf, ScopeOf
    , ITerm(..), iVal, iType, iScope, iAnn
    ) where

import AST
import Control.Lens (makeLenses)

type family TypeOf (t :: Knot -> *) :: Knot -> *
type family ScopeOf (t :: Knot -> *) :: Knot -> *

-- | Knot for terms, annotating them with inference results
--
-- 'e' may vary in different sub-terms, allowing differently typed
-- type annotations and scopes.
--
-- See also `AST.Class.Infer.Inferred.Inferred`, a newtype wrapper
-- knotted by `v` whose children are the types.
data ITerm a v e = ITerm
    { _iVal :: Tie e (ITerm a v)
    , _iType :: Tree v (TypeOf (RunKnot e))
    , _iScope :: Tree (ScopeOf (RunKnot e)) v
    , _iAnn :: a
    }
makeLenses ''ITerm
