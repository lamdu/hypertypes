{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TupleSections, FlexibleInstances #-}

module AST.Term.Var
    ( Var(..), _Var
    , MonadScopeTypes(..)
    ) where

import           AST.Class.Infer (Infer(..), TypeAST)
import           AST.Class.Recursive (Recursive)
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Knot (Knot, Tree)
import           AST.Unify (MonadUnify, Unify, UVar)
import           Control.DeepSeq (NFData)
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           GHC.Generics (Generic)

import           Prelude.Compat

-- | Parametrized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: Knot -> *) (f :: Knot) = Var v
    deriving (Eq, Ord, Show, Generic, Binary, NFData)
Lens.makePrisms ''Var

makeChildrenRecursive [''Var]

class MonadScopeTypes v t m where
    scopeType :: v -> m (Tree (UVar m) t)
    localScopeType :: v -> m (Tree (UVar m) t) -> m a -> m a

type instance TypeAST (Var v t) = TypeAST t

instance
    ( MonadUnify m
    , Recursive (Unify m) (TypeAST expr)
    , MonadScopeTypes v (TypeAST expr) m
    ) =>
    Infer m (Var v expr) where

    infer (Var x) = scopeType x <&> (, Var x)
