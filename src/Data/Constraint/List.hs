{-# LANGUAGE PolyKinds, UndecidableSuperClasses, FlexibleInstances #-}

module Data.Constraint.List
    ( NoConstraint, And
    ) where

class    NoConstraint x
instance NoConstraint x

class    (c0 x, c1 x) => And c0 c1 x
instance (c0 x, c1 x) => And c0 c1 x
