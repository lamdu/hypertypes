{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, LambdaCase, EmptyCase #-}
{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses, TupleSections, DataKinds #-}

module AST.Term.Scope
    ( Scope(..), _Scope
    , ScopeVar(..), _ScopeVar
    , EmptyScope
    , DeBruijnIndex(..), inverseDeBruijnIndex
    , scope, scopeVar
    , ScopeTypes, HasScopeTypes(..)
    ) where

import           AST.Class.Children (Children)
import           AST.Class.Infer (Infer(..), inferNode, iType, TypeOf)
import           AST.Class.Infer.Infer1 (Infer1(..), HasTypeOf1(..))
import           AST.Class.Recursive (Recursive(..))
import           AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import           AST.Knot (Knot, Tie, Tree)
import           AST.Term.FuncType
import           AST.Unify (Unify(..), UVar, newUnbound, newTerm)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint (Dict(..), withDict, (:-), (\\))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data EmptyScope

newtype Scope expr a k = Scope (Tie k (expr (Maybe a)))
Lens.makePrisms ''Scope

newtype ScopeVar (expr :: * -> Knot -> *) a (k :: Knot) = ScopeVar a
Lens.makePrisms ''ScopeVar

makeChildrenAndZipMatch [''Scope, ''ScopeVar]
instance Recursive Children (expr (Maybe a)) => Recursive Children (Scope expr a)

class DeBruijnIndex a where
    deBruijnIndex :: Prism' Int a
    deBruijnIndexMax :: Proxy a -> Int

instance DeBruijnIndex EmptyScope where
    deBruijnIndex = Lens.prism (\case) Left
    deBruijnIndexMax _ = -1

instance DeBruijnIndex a => DeBruijnIndex (Maybe a) where
    deBruijnIndex =
        Lens.prism' toInt fromInt
        where
            toInt Nothing = 0
            toInt (Just x) = 1 + deBruijnIndex # x
            fromInt x
                | x == 0 = Just Nothing
                | otherwise = (x - 1) ^? deBruijnIndex <&> Just
    deBruijnIndexMax _ = 1 + deBruijnIndexMax (Proxy :: Proxy a)

inverseDeBruijnIndex :: forall a. DeBruijnIndex a => Prism' Int a
inverseDeBruijnIndex =
    Lens.iso (l -) (l -) . deBruijnIndex
    where
        l = deBruijnIndexMax (Proxy :: Proxy a)

scope ::
    forall expr a f.
    DeBruijnIndex a =>
    (Int -> Tree f (expr (Maybe a))) ->
    Tree (Scope expr a) f
scope f = Scope (f (inverseDeBruijnIndex # (Nothing :: Maybe a)))

scopeVar :: DeBruijnIndex a => Int -> ScopeVar expr a f
scopeVar x = ScopeVar (x ^?! inverseDeBruijnIndex)

type ScopeTypes v t = Seq (Tree v t)

class HasScopeTypes v t env where
    scopeTypes :: Lens' env (ScopeTypes v t)

instance HasScopeTypes v t (ScopeTypes v t) where
    scopeTypes = id

type instance TypeOf (Scope t k) = TypeOf (t k)
type instance TypeOf (ScopeVar t k) = TypeOf (t k)
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
    , HasScopeTypes (UVar m) (TypeOf1 t) env
    ) =>
    Infer m (Scope t k) where

    infer (Scope x) =
        withDict (typeAst (Proxy :: Proxy (t k))) $
        withDict (typeAst (Proxy :: Proxy (t (Maybe k)))) $
        do
            varType <- newUnbound
            xI <-
                local
                (scopeTypes %~ (varType Sequence.<|))
                (inferNode x)
            funcType # FuncType
                { _funcIn = varType
                , _funcOut = xI ^. iType
                } & newTerm
                <&> (, Scope xI)
        \\ (inferMonad :: DeBruijnIndex (Maybe k) :- Infer m (t (Maybe k)))

instance
    ( Recursive (Unify m) (TypeOf (t k))
    , MonadReader env m
    , HasScopeTypes (UVar m) (TypeOf (t k)) env
    , DeBruijnIndex k
    ) =>
    Infer m (ScopeVar t k) where

    infer (ScopeVar v) =
        Lens.view scopeTypes
        <&> (`Sequence.index` (deBruijnIndex # v))
        <&> (, ScopeVar v)
