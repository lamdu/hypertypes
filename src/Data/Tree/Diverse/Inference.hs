{-# LANGUAGE NoImplicitPrelude, TypeFamilies, MultiParamTypeClasses, FlexibleContexts #-}

module Data.Tree.Diverse.Inference
    where

import           Data.Functor.Identity (Identity(..))
import           Data.Tree.Diverse
import           Data.Tree.Diverse.Unification

import           Prelude.Compat

type family TypeOf (t :: (* -> *) -> *) :: (* -> *) -> *

class UnifyMonad (TypeOf t) m => InferMonad t m where
    inferBody :: t (Ann a) -> m (Node (UTerm (Var (TypeOf t) m)) (TypeOf t))
