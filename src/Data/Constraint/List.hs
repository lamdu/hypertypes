{-# LANGUAGE PolyKinds #-}

module Data.Constraint.List
    ( ApplyConstraints
    ) where

import Data.Constraint (Constraint)

type family ApplyConstraints cs a :: Constraint where
    ApplyConstraints (c ': cs) a = (c a, ApplyConstraints cs a)
    ApplyConstraints '[] a = ()
