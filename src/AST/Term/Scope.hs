{-# LANGUAGE NoImplicitPrelude, StandaloneDeriving, UndecidableInstances, TemplateHaskell, KindSignatures, TypeFamilies, LambdaCase, EmptyCase, ScopedTypeVariables, TypeOperators, FlexibleInstances, MultiParamTypeClasses, TupleSections, DataKinds #-}

module AST.Term.Scope
    ( Scope(..), ScopeVar(..), EmptyScope
    , DeBruijnIndex(..)
    , scope, scopeVar
    , ScopeTypes, HasScopeTypes(..)
    ) where

import           AST.Class.Infer (Infer(..), inferNode, nodeType, TypeAST, FuncType(..))
import           AST.Class.Infer.Infer1 (Infer1(..), HasTypeAST1(..))
import           AST.Class.Children (Children)
import           AST.Class.Recursive (Recursive(..), RecursiveConstraint)
import           AST.Class.ZipMatch.TH (makeChildrenAndZipMatch)
import           AST.Knot (Knot, Tie, Tree)
import           AST.Unify (Unify(..), Binding(..), UniVar, newTerm)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint (Dict(..), withDict, (:-), (\\))
import           Data.IntMap (IntMap)
import           Data.Maybe (fromMaybe)
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data EmptyScope

newtype Scope expr a k = Scope (Tie k (expr (Maybe a)))
newtype ScopeVar (expr :: * -> Knot -> *) a (k :: Knot) = ScopeVar a

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

type ScopeTypes v t = IntMap (Tree v t)

class HasScopeTypes v t env where
    scopeTypes :: Lens' env (ScopeTypes v t)

instance HasScopeTypes v t (ScopeTypes v t) where
    scopeTypes = id

type instance TypeAST (Scope t k) = TypeAST (t k)
type instance TypeAST (ScopeVar t k) = TypeAST (t k)
instance HasTypeAST1 t => HasTypeAST1 (Scope t) where
    type TypeAST1 (Scope t) = TypeAST1 t
    type TypeASTIndexConstraint (Scope t) = DeBruijnIndex
    typeAst p = withDict (typeAst p) Dict
instance HasTypeAST1 t => HasTypeAST1 (ScopeVar t) where
    type TypeAST1 (ScopeVar t) = TypeAST1 t
    type TypeASTIndexConstraint (ScopeVar t) = DeBruijnIndex
    typeAst p = withDict (typeAst p) Dict

instance
    ( HasTypeAST1 t
    , FuncType (TypeAST1 t)
    , Infer1 m t
    , Recursive (Unify m) (TypeAST (t k))
    , TypeASTIndexConstraint t ~ DeBruijnIndex
    , DeBruijnIndex k
    , MonadReader env m
    , HasScopeTypes (UniVar m) (TypeAST1 t) env
    ) =>
    Infer m (Scope t k) where

    infer (Scope x) =
        withDict (recursive :: Dict (RecursiveConstraint (TypeAST (t k)) (Unify m))) $
        withDict (typeAst (Proxy :: Proxy (t k))) $
        withDict (typeAst (Proxy :: Proxy (t (Maybe k)))) $
        do
            varType <- newVar (binding :: Binding m (TypeAST1 t))
            xI <-
                local
                (scopeTypes . Lens.at (deBruijnIndexMax (Proxy :: Proxy (Maybe k))) ?~ varType)
                (inferNode x)
            funcType # (varType, xI ^. nodeType) & newTerm
                <&> (, Scope xI)
        \\ (inferMonad :: DeBruijnIndex (Maybe k) :- Infer m (t (Maybe k)))

instance
    ( Recursive (Unify m) (TypeAST (t k))
    , MonadReader env m
    , HasScopeTypes (UniVar m) (TypeAST (t k)) env
    , DeBruijnIndex k
    ) =>
    Infer m (ScopeVar t k) where

    infer (ScopeVar v) =
        Lens.view (scopeTypes . Lens.at (inverseDeBruijnIndex # v))
        <&> fromMaybe (error "name error")
        <&> (, ScopeVar v)
