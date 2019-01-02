{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TupleSections, FlexibleInstances #-}

module AST.Term.Var
    ( Var(..), _Var
    , MonadScopeTypes(..)
    ) where

import           AST.Class.Infer (Infer(..), TypeOf)
import           AST.Class.Recursive (Recursive)
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Knot (Knot, Tree)
import           AST.Unify (Unify, UVar)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

-- | Parametrized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: Knot -> *) (k :: Knot) = Var v
    deriving (Eq, Ord, Show, Generic, Binary, NFData)
Lens.makePrisms ''Var

makeChildrenRecursive [''Var]

instance Pretty v => Pretty (Var v expr k) where
    pPrintPrec lvl p (Var v) = pPrintPrec lvl p v

class MonadScopeTypes v t m where
    scopeType :: v -> m (Tree (UVar m) t)
    localScopeType :: v -> m (Tree (UVar m) t) -> m a -> m a

type instance TypeOf (Var v t) = TypeOf t

instance
    ( Recursive (Unify m) (TypeOf expr)
    , MonadScopeTypes v (TypeOf expr) m
    ) =>
    Infer m (Var v expr) where

    infer (Var x) = scopeType x <&> (, Var x)
