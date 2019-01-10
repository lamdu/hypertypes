{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, DataKinds, DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TupleSections, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, ConstraintKinds #-}

module AST.Term.Var
    ( Var(..), _Var
    ) where

import           AST.Class.Children.TH (makeChildren)
import           AST.Class.Infer (Infer(..), HasScope(..), ScopeLookup(..), TypeOf, ScopeOf)
import           AST.Class.Recursive (Recursive)
import           AST.Class.Unify (Unify)
import           AST.Knot (Knot)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

-- | Parametrized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: Knot -> *) (k :: Knot) = Var v
    deriving (Eq, Ord, Show, Generic, Binary, NFData)

Lens.makePrisms ''Var
makeChildren ''Var

instance c (Var v expr) => Recursive c (Var v expr)

instance Pretty v => Pretty (Var v expr k) where
    pPrintPrec lvl p (Var v) = pPrintPrec lvl p v

type instance TypeOf  (Var v t) = TypeOf  t
type instance ScopeOf (Var v t) = ScopeOf t

instance
    ( Recursive (Unify m) (TypeOf expr)
    , HasScope m (ScopeOf expr)
    , ScopeLookup v expr
    ) =>
    Infer m (Var v expr) where

    infer (Var x) =
        getScope >>= scopeType (Proxy :: Proxy expr) x <&> (, Var x)
