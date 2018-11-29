{-# LANGUAGE TemplateHaskell, FlexibleContexts, TypeFamilies #-}

module GhcStuck where

import AST
import AST.Unify

newtype Typ f = Typ (f Int)

instance Children Typ where
    type ChildrenConstraint Typ constraint = constraint Typ

-- Replacing `Typ` with `t` doesn't cause GHC to be stuck
t :: UnifyMonad m Typ => m (t a)
t = undefined
