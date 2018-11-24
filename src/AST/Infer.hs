{-# LANGUAGE NoImplicitPrelude, MultiParamTypeClasses, FlexibleContexts #-}

module AST.Infer
    where

import           AST
import           AST.Ann
import           AST.Unify
import           Data.Functor.Identity (Identity(..))

import           Prelude.Compat

class UnifyMonad v t m => InferMonad e v t m where
    inferBody :: e (Ann a) -> m (Node (UTerm v) t)
