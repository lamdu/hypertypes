{-# LANGUAGE NoImplicitPrelude, KindSignatures, DataKinds, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, ConstraintKinds, UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Combinators for partially applied constraints on knots

module AST.Class.Combinators
    ( And
    , TieHasConstraint
    ) where

import AST.Knot (Knot, Tie)

class    (c0 k, c1 k) => And c0 c1 (k :: Knot -> *)
instance (c0 k, c1 k) => And c0 c1 k

class    constraint (Tie outer k) => TieHasConstraint constraint outer k
instance constraint (Tie outer k) => TieHasConstraint constraint outer k
