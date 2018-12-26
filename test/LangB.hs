{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, TypeFamilies, FlexibleInstances, UndecidableInstances, TupleSections, ScopedTypeVariables, GeneralizedNewtypeDeriving, DataKinds #-}

module LangB where

import TypeLang

import AST
import AST.Class.Infer
import AST.Unify
import AST.Term.Apply
import AST.Term.Lam
import AST.Term.Let
import AST.Term.Var
import AST.Unify.IntMapBinding
import AST.Unify.STBinding
import AST.Unify.Term
import Control.Applicative
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST(..))
import Control.Monad.Trans.Maybe
import Data.Constraint
import Data.Map
import Data.Maybe

data LangB k
    = BLit Int
    | BApp (Apply LangB k)
    | BVar (Var String LangB k)
    | BLam (Lam String LangB k)
    | BLet (Let String LangB k)

makeChildrenRecursive [''LangB]

type instance TypeAST LangB = Typ

instance (MonadInfer m, MonadScopeTypes [Char] Typ m, Recursive (Unify m) Typ) => Infer m LangB where
    infer (BLit x) =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        newTerm TInt <&> (, BLit x)
    infer (BApp x) = infer x <&> _2 %~ BApp
    infer (BVar x) = infer x <&> _2 %~ BVar
    infer (BLam x) = infer x <&> _2 %~ BLam
    infer (BLet x) = infer x <&> _2 %~ BLet

-- Monads for inferring `LangB`:

newtype IntInferB a =
    IntInferB (RWST (Map String (IntInferB (Tree (Const Int) Typ)), InferLevel) () IntInferState Maybe a)
    deriving
    ( Functor, Applicative, Alternative, Monad
    , MonadReader (Map String (IntInferB (Tree (Const Int) Typ)), InferLevel)
    , MonadState IntInferState
    )

type instance UVar IntInferB = Const Int

instance MonadScopeTypes String Typ IntInferB where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadInfer IntInferB where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Unify IntInferB Typ where
    binding = intBindingState (Lens._1 . tTyp)
    newQuantifiedVariable _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Unify IntInferB Row where
    binding = intBindingState (Lens._1 . tRow)
    newQuantifiedVariable _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show

instance Recursive (Unify IntInferB) Typ
instance Recursive (Unify IntInferB) Row

newtype STInferB s a =
    STInferB
    (ReaderT (Map String (STInferB s (Tree (STVar s) Typ)), InferLevel, STInferState s) (MaybeT (ST s)) a)
    deriving
    ( Functor, Applicative, Alternative, Monad, MonadST
    , MonadReader (Map String (STInferB s (Tree (STVar s) Typ)), InferLevel, STInferState s)
    )

type instance UVar (STInferB s) = STVar s

instance MonadScopeTypes String Typ (STInferB s) where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadInfer (STInferB s) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Unify (STInferB s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tTyp) <&> ('t':) . show

instance Unify (STInferB s) Row where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tRow) <&> ('r':) . show

instance Recursive (Unify (STInferB s)) Typ
instance Recursive (Unify (STInferB s)) Row
