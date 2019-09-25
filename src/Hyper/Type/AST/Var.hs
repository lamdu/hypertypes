-- | Variables.

{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, EmptyCase #-}
{-# LANGUAGE FlexibleInstances, TemplateHaskell, FlexibleContexts #-}

module Hyper.Type.AST.Var
    ( Var(..), _Var
    , VarType(..)
    , ScopeOf, HasScope(..)
    ) where

import           Hyper
import           Hyper.Infer
import           Hyper.Unify (Unify, UVarOf)
import           Control.DeepSeq (NFData)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Proxy (Proxy(..))
import           GHC.Generics (Generic)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

type family ScopeOf (t :: HyperType) :: HyperType

class HasScope m s where
    getScope :: m (Tree s (UVarOf m))

class VarType var expr where
    -- | Instantiate a type for a variable in a given scope
    varType ::
        Unify m (TypeOf expr) =>
        Proxy expr -> var -> Tree (ScopeOf expr) (UVarOf m) ->
        m (Tree (UVarOf m) (TypeOf expr))

-- | Parameterized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: AHyperType -> *) (k :: AHyperType) = Var v
    deriving newtype (Eq, Ord, Binary, NFData)
    deriving stock (Show, Generic)

Lens.makePrisms ''Var
makeKTraversableApplyAndBases ''Var
makeZipMatch ''Var

instance Pretty v => Pretty (Var v expr k) where
    pPrintPrec lvl p (Var v) = pPrintPrec lvl p v

type instance InferOf (Var v t) = ANode (TypeOf t)

instance
    ( Unify m (TypeOf expr)
    , HasScope m (ScopeOf expr)
    , VarType v expr
    , Monad m
    ) =>
    Infer m (Var v expr) where

    {-# INLINE inferBody #-}
    inferBody (Var x) =
        getScope >>= varType (Proxy @expr) x <&> MkANode <&> (Var x, )
