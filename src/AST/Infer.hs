{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Infer
    where

import           AST
import           AST.Ann
import           AST.Unify
import           Data.Functor.Identity (Identity(..))

import           Prelude.Compat

type family TypeOf (t :: (* -> *) -> *) :: (* -> *) -> *

class UnifyMonad (TypeOf t) m => InferMonad t m where
    inferBody :: t (Ann a) -> m (Node (UTerm (Var (TypeOf t) m)) (TypeOf t))
