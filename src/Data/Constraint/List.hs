{-# LANGUAGE PolyKinds, UndecidableSuperClasses, FlexibleInstances #-}

module Data.Constraint.List
    ( And
    ) where

-- | A class expressing that two constraints apply to a type constructor
class    (c0 x, c1 x) => And c0 c1 x
instance (c0 x, c1 x) => And c0 c1 x
