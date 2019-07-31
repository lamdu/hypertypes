{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds, FlexibleContexts #-}

module AST.Term.Var
    ( Var(..), _Var
    , VarType(..)
    ) where

import           AST
import           AST.Infer
import           AST.Unify (Unify, UVarOf)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Functor.Const (Const)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

class VarType var expr where
    -- | Instantiate a type for a variable in a given scope
    varType ::
        Recursively (Unify m) (TypeOf expr) =>
        Proxy expr -> var -> Tree (ScopeOf expr) (UVarOf m) ->
        m (Tree (UVarOf m) (TypeOf expr))

-- | Parameterized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: Knot -> *) (k :: Knot) = Var v
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

instance KNodes (Var v e) where
    type NodeTypesOf (Var v e) = Const ()
    type NodesConstraint (Var v e) = KnotsConstraint '[]

Lens.makePrisms ''Var
makeKTraversableAndBases ''Var

instance c (Var v expr) => Recursively c (Var v expr)

instance Pretty v => Pretty (Var v expr k) where
    pPrintPrec lvl p (Var v) = pPrintPrec lvl p v

type instance TypeOf  (Var v t) = TypeOf  t
type instance ScopeOf (Var v t) = ScopeOf t

instance
    ( Recursively (Unify m) (TypeOf expr)
    , HasScope m (ScopeOf expr)
    , VarType v expr
    ) =>
    Infer m (Var v expr) where

    {-# INLINE inferBody #-}
    inferBody (Var x) =
        getScope >>= varType (Proxy :: Proxy expr) x <&> InferRes (Var x)
