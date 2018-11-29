{-# LANGUAGE FlexibleContexts #-}

module GhcStuck where

import AST.Unify
import TypeLang

-- Replacing `Typ` with `t` doesn't cause GHC to be stuck
t :: UnifyMonad m Typ => m (t a)
t = undefined
