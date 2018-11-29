{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, UndecidableSuperClasses, KindSignatures #-}

module AST.Unify where

import AST

class ChildrenConstraint t (UnifyMonad m) => UnifyMonad (m :: * -> *) t where
