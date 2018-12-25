{-# LANGUAGE NoImplicitPrelude, TemplateHaskell, KindSignatures, DataKinds, DeriveGeneric, GeneralizedNewtypeDeriving, TupleSections, MultiParamTypeClasses, TypeFamilies, FlexibleInstances, UndecidableInstances #-}

module AST.Term.Var
    ( Var(..), _Var
    , HasScopeTypes(..)
    ) where

import           AST.Class.Infer (MonadInfer, Infer(..), TypeAST)
import           AST.Class.Recursive (Recursive)
import           AST.Class.Recursive.TH (makeChildrenRecursive)
import           AST.Knot (Knot, Tree)
import           AST.Unify (Unify, UniVar)
import           Control.DeepSeq (NFData)
import           Control.Lens (Lens')
import           Control.Lens.Operators
import qualified Control.Lens as Lens
import           Control.Monad.Reader (MonadReader)
import           Data.Binary (Binary)
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import           GHC.Generics (Generic)

import           Prelude.Compat

-- | Parametrized by term AST and not by its type AST
-- (which currently is its only part used),
-- for future evaluation/complilation support.
newtype Var v (expr :: Knot -> *) (f :: Knot) = Var v
    deriving (Eq, Ord, Show, Generic, Binary, NFData)
Lens.makePrisms ''Var

makeChildrenRecursive [''Var]

class Ord v => HasScopeTypes v u t env where
    scopeTypes :: Lens' env (Map v (Tree u t))

instance Ord v => HasScopeTypes v u t (Map v (Tree u t)) where
    scopeTypes = id

type instance TypeAST (Var v t) = TypeAST t

instance
    ( MonadInfer m
    , Recursive (Unify m) (TypeAST expr)
    , MonadReader env m
    , HasScopeTypes v (UniVar m) (TypeAST expr) env
    ) =>
    Infer m (Var v expr) where

    infer (Var x) =
        Lens.view (scopeTypes . Lens.at x)
        <&> fromMaybe (error "name error")
        <&> (, Var x)
