{-# LANGUAGE PolyKinds, UndecidableSuperClasses, FlexibleInstances #-}

module Data.Constraint.List
    ( ApplyConstraints, And
    ) where

import Data.Constraint (Constraint)

type family ApplyConstraints cs a :: Constraint where
    ApplyConstraints (c ': cs) a = (c a, ApplyConstraints cs a)
    ApplyConstraints '[] a = ()

class    (c0 x, c1 x) => And c0 c1 x
instance (c0 x, c1 x) => And c0 c1 x
