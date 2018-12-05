{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, TemplateHaskell, KindSignatures, TypeFamilies, LambdaCase, EmptyCase, ScopedTypeVariables #-}

module AST.Scope where

import           AST
import           AST.Recursive
import           AST.TH
import           Data.Proxy

import           Prelude.Compat

data EmptyScope

newtype Scope expr a f = Scope (Node f (expr (Maybe a)))

makeChildrenAndZipMatch [''Scope]
instance ChildrenRecursive (expr (Maybe a)) => ChildrenRecursive (Scope expr a)

class DeBruijnIndex a where
    deBruijnIndex :: a -> Int
    deBruijnIndexMax :: Proxy a -> Int

instance DeBruijnIndex EmptyScope where
    deBruijnIndex = \case
    deBruijnIndexMax _ = -1

instance DeBruijnIndex a => DeBruijnIndex (Maybe a) where
    deBruijnIndex Nothing = 0
    deBruijnIndex (Just x) = 1 + deBruijnIndex x
    deBruijnIndexMax _ = 1 + deBruijnIndexMax (Proxy :: Proxy a)

inverseDeBruijnIndex :: forall a. DeBruijnIndex a => a -> Int
inverseDeBruijnIndex x = deBruijnIndexMax (Proxy :: Proxy a) - deBruijnIndex x
