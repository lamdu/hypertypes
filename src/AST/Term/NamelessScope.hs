{-# LANGUAGE NoImplicitPrelude, UndecidableInstances, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, LambdaCase, EmptyCase, ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, DataKinds, DerivingStrategies #-}

module AST.Term.NamelessScope
    ( Scope(..), _Scope
    , ScopeVar(..), _ScopeVar
    , EmptyScope
    , DeBruijnIndex(..)
    , ScopeTypes(..), _ScopeTypes, HasScopeTypes(..)
    ) where

import           AST
import           AST.Class.Infer.Infer1 (Infer1(..), HasTypeOf1(..))
import           AST.Combinator.Single (Single)
import           AST.Infer
import           AST.Term.FuncType
import           AST.Unify (Unify(..), UVarOf)
import           AST.Unify.New (newTerm, newUnbound)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint (Dict(..), withDict, (:-), (\\))
import           Data.Functor.Const (Const)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data EmptyScope

newtype Scope expr a k = Scope (Node k (expr (Maybe a)))
Lens.makePrisms ''Scope

instance HasNodes (Scope e a) where
    type NodeTypesOf (Scope e a) = Single (e (Maybe a))

newtype ScopeVar (expr :: * -> Knot -> *) a (k :: Knot) = ScopeVar a
Lens.makePrisms ''ScopeVar

instance HasNodes (ScopeVar e a) where
    type NodeTypesOf (ScopeVar e a) = Const ()

makeZipMatch ''Scope
makeKApplicativeBases ''Scope
makeKTraversableAndFoldable ''Scope
makeZipMatch ''ScopeVar
makeKTraversableAndBases ''ScopeVar
instance (c (Scope expr a), Recursive c (expr (Maybe a))) => Recursive c (Scope expr a)

class DeBruijnIndex a where
    deBruijnIndex :: Prism' Int a

instance DeBruijnIndex EmptyScope where
    deBruijnIndex = Lens.prism (\case{}) Left

instance DeBruijnIndex a => DeBruijnIndex (Maybe a) where
    deBruijnIndex =
        Lens.prism' toInt fromInt
        where
            toInt Nothing = 0
            toInt (Just x) = 1 + deBruijnIndex # x
            fromInt x
                | x == 0 = Just Nothing
                | otherwise = (x - 1) ^? deBruijnIndex <&> Just

newtype ScopeTypes t v = ScopeTypes (Seq (Node v t))
    deriving newtype (Semigroup, Monoid)

instance HasNodes (ScopeTypes t) where
    type NodeTypesOf (ScopeTypes t) = Single t

Lens.makePrisms ''ScopeTypes
makeKTraversableAndBases ''ScopeTypes

-- TODO: Replace this class with ones from Infer
class HasScopeTypes v t env where
    scopeTypes :: Lens' env (Tree (ScopeTypes t) v)

instance HasScopeTypes v t (Tree (ScopeTypes t) v) where
    scopeTypes = id

type instance TypeOf (Scope t k) = TypeOf (t k)
type instance TypeOf (ScopeVar t k) = TypeOf (t k)
type instance ScopeOf (Scope t k) = ScopeTypes (TypeOf (t k))
type instance ScopeOf (ScopeVar t k) = ScopeTypes (TypeOf (t k))
instance HasTypeOf1 t => HasTypeOf1 (Scope t) where
    type TypeOf1 (Scope t) = TypeOf1 t
    type TypeOfIndexConstraint (Scope t) = DeBruijnIndex
    typeAst p = withDict (typeAst p) Dict
instance HasTypeOf1 t => HasTypeOf1 (ScopeVar t) where
    type TypeOf1 (ScopeVar t) = TypeOf1 t
    type TypeOfIndexConstraint (ScopeVar t) = DeBruijnIndex
    typeAst p = withDict (typeAst p) Dict

instance
    ( HasTypeOf1 t
    , HasFuncType (TypeOf1 t)
    , Infer1 m t
    , Recursive (Unify m) (TypeOf (t k))
    , TypeOfIndexConstraint t ~ DeBruijnIndex
    , DeBruijnIndex k
    , MonadReader env m
    , HasScopeTypes (UVarOf m) (TypeOf1 t) env
    , HasScope m (ScopeTypes (TypeOf (t k)))
    ) =>
    Infer m (Scope t k) where

    inferBody (Scope x) =
        withDict (typeAst (Proxy :: Proxy (t k))) $
        withDict (typeAst (Proxy :: Proxy (t (Maybe k)))) $
        do
            varType <- newUnbound
            InferredChild xI xT <-
                inferChild x
                & local (scopeTypes . _ScopeTypes %~ (varType Sequence.<|))
            funcType # FuncType varType xT & newTerm <&> InferRes (Scope xI)
        \\ (inferMonad :: DeBruijnIndex (Maybe k) :- Infer m (t (Maybe k)))

instance
    ( Recursive (Unify m) (TypeOf (t k))
    , MonadReader env m
    , HasScopeTypes (UVarOf m) (TypeOf (t k)) env
    , DeBruijnIndex k
    , HasScope m (ScopeTypes (TypeOf (t k)))
    ) =>
    Infer m (ScopeVar t k) where

    inferBody (ScopeVar v) =
        Lens.view (scopeTypes . _ScopeTypes)
        <&> (^?! Lens.ix (deBruijnIndex # v))
        <&> InferRes (ScopeVar v)
