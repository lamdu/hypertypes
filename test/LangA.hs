{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, LambdaCase, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, DataKinds, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, TypeOperators #-}

-- | A test language with locally-nameless variable scoping and type signatures with for-alls

module LangA where

import TypeLang

import AST
import AST.Class.Combinators
import AST.Class.Infer
import AST.Class.Infer.Infer1
import AST.Term.Apply
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.TypeSig
import AST.Unify
import AST.Unify.IntMapBinding
import AST.Unify.QuantificationScope
import AST.Unify.STBinding
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
    , Recursive (And (Unify m) (HasChild Types)) Typ
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

instance MonadUnify IntInferA where
    type ScopeConstraints IntInferA = QuantificationScope
    scopeConstraints = Lens.view Lens._2

instance MonadInfer IntInferA where
    localLevel = local (Lens._2 . _QuantificationScope +~ 1)

instance Unify IntInferA Typ where
    binding = intBindingState (Lens._1 . tTyp)
    newQuantifiedVariable _ _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Unify IntInferA Row where
    binding = intBindingState (Lens._1 . tRow)
    newQuantifiedVariable _ _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show

instance Recursive (Unify IntInferA) Typ
instance Recursive (Unify IntInferA) Row
instance Recursive (Unify IntInferA `And` HasChild Types) Typ
instance Recursive (Unify IntInferA `And` HasChild Types) Row

newtype STInferA s a =
    STInferA (ReaderT (ScopeTypes (STVar s) Typ, QuantificationScope, STInferState s) (MaybeT (ST s)) a)
    deriving
    ( Functor, Applicative, Alternative, Monad, MonadST
    , MonadReader (ScopeTypes (STVar s) Typ, QuantificationScope, STInferState s)
    )

type instance UVar (STInferA s) = STVar s

instance MonadUnify (STInferA s) where
    type ScopeConstraints (STInferA s) = QuantificationScope
    scopeConstraints = Lens.view Lens._2

instance MonadInfer (STInferA s) where
    localLevel = local (Lens._2 . _QuantificationScope +~ 1)

instance Unify (STInferA s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tTyp) <&> ('t':) . show

instance Unify (STInferA s) Row where
    binding = stBindingState
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tRow) <&> ('r':) . show

instance Recursive (Unify (STInferA s)) Typ
instance Recursive (Unify (STInferA s)) Row
instance Recursive (Unify (STInferA s) `And` HasChild Types) Typ
instance Recursive (Unify (STInferA s) `And` HasChild Types) Row
