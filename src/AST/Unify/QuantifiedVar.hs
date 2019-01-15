{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module AST.Unify.QuantifiedVar
    ( HasQuantifiedVar(..)
    , MonadQuantify(..)
    , QVarHasInstance
    ) where

import AST.Knot (Knot)
import Control.Lens (Prism')

class HasQuantifiedVar (t :: Knot -> *) where
    type family QVar t
    quantifiedVar :: Prism' (t f) (QVar t)

class cls (QVar t) => QVarHasInstance cls t
instance cls (QVar t) => QVarHasInstance cls t

class MonadQuantify typeConstraints q m where
    newQuantifiedVariable :: typeConstraints -> m q
