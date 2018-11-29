{-# LANGUAGE TypeFamilies, UndecidableInstances, UndecidableSuperClasses, MultiParamTypeClasses, FlexibleContexts #-}

import GHC.Exts (Constraint)

type family ChildrenConstraint expr (constraint :: * -> Constraint) :: Constraint

class ChildrenConstraint t (UnifyMonad m) => UnifyMonad m t where

newtype Typ = Typ Int

type instance ChildrenConstraint Typ constraint = constraint Typ

-- Replacing `Typ` with `t` doesn't cause GHC to be stuck
t :: UnifyMonad m Typ => (m, t)
t = undefined
