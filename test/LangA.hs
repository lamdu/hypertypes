{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, LambdaCase, MultiParamTypeClasses, FlexibleInstances, DataKinds, TupleSections, ConstraintKinds, FlexibleContexts, GeneralizedNewtypeDeriving #-}

-- | A test language with locally-nameless variable scoping and type signatures with for-alls

module LangA where

import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Infer.Infer1
import AST.Term.Apply
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.TypeSig
import AST.Unify
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

data LangA v f
    = ALam (Scope LangA v f)
    | AVar (ScopeVar LangA v f)
    | AApp (Apply (LangA v) f)
    | ATypeSig (TypeSig (Tree Pure (Scheme Types Typ)) (LangA v) f)
    | ALit Int

makeChildrenRecursive [''LangA]
instance Recursive Children (LangA v)

type instance TypeAST (LangA k) = Typ

instance HasTypeAST1 LangA where
    type TypeAST1 LangA = Typ
    type TypeASTIndexConstraint LangA = DeBruijnIndex
    typeAst _ = Dict

type TermInfer1Deps env m =
    ( MonadInfer m
    , MonadReader env m
    , HasScopeTypes (UVar m) Typ env
    , Recursive (Unify m) Typ
    , Recursive (CanInstantiate m Types) Typ
    , ChildrenConstraint Types (Unify m)
    )

instance TermInfer1Deps env m => Infer1 m LangA where
    inferMonad = Sub Dict

instance (DeBruijnIndex k, TermInfer1Deps env m) => Infer m (LangA k) where
    infer (ALit     x) = newTerm TInt <&> (, ALit x)
    infer (AVar     x) = infer x <&> _2 %~ AVar
    infer (ALam     x) = infer x <&> _2 %~ ALam
    infer (AApp     x) = infer x <&> _2 %~ AApp
    infer (ATypeSig x) = infer x <&> _2 %~ ATypeSig

-- Monads for inferring `LangA`:

newtype IntInferA a = IntInferA (RWST (ScopeTypes (Const Int) Typ, QuantificationScope) () IntInferState Maybe a)
    deriving
    ( Functor, Applicative, Alternative, Monad
    , MonadReader (ScopeTypes (Const Int) Typ, QuantificationScope)
    , MonadState IntInferState
    )

type instance UVar IntInferA = Const Int

instance MonadInfer IntInferA where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _QuantificationScope +~ 1)

instance Unify IntInferA Typ where
    binding = intBindingState (Lens._1 . tTyp)
    newQuantifiedVariable _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Unify IntInferA Row where
    binding = intBindingState (Lens._1 . tRow)
    newQuantifiedVariable _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show

instance Recursive (Unify IntInferA) Typ
instance Recursive (Unify IntInferA) Row
instance Recursive (CanInstantiate IntInferA Types) Typ
instance Recursive (CanInstantiate IntInferA Types) Row

newtype STInferA s a =
    STInferA (ReaderT (ScopeTypes (STVar s) Typ, QuantificationScope, STInferState s) (MaybeT (ST s)) a)
    deriving
    ( Functor, Applicative, Alternative, Monad, MonadST
    , MonadReader (ScopeTypes (STVar s) Typ, QuantificationScope, STInferState s)
    )

type instance UVar (STInferA s) = STVar s

instance MonadInfer (STInferA s) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _QuantificationScope +~ 1)

instance Unify (STInferA s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tTyp) <&> ('t':) . show

instance Unify (STInferA s) Row where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tRow) <&> ('r':) . show

instance Recursive (Unify (STInferA s)) Typ
instance Recursive (Unify (STInferA s)) Row
instance Recursive (CanInstantiate (STInferA s) Types) Typ
instance Recursive (CanInstantiate (STInferA s) Types) Row
