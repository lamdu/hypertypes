{-# LANGUAGE NoImplicitPrelude, DataKinds, TypeFamilies, RankNTypes, ConstraintKinds #-}

module AST.Class.Pointed
    ( KPointed(..)
    ) where

import AST.Knot
import Data.Constraint (Constraint)
import Data.Proxy (Proxy)

-- | Construct knotted values using `RankNTypes` field constructors
class KPointed (k :: Knot -> *) where
    pureK ::
        (forall child. Tree n child) ->
        Tree k n

    type KLiftConstraint k (c :: (Knot -> *) -> Constraint) :: Constraint

    pureKWith ::
        KLiftConstraint k constraint =>
        Proxy constraint ->
        (forall child. constraint child => Tree n child) ->
        Tree k n
