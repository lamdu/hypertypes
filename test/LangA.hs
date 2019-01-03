{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, LambdaCase, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, DataKinds, TupleSections, ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}

-- | A test language with locally-nameless variable scoping and type signatures with for-alls

module LangA where

import           TypeLang

import           AST
import           AST.Class.Infer
import           AST.Class.Infer.Infer1
import           AST.Class.Infer.ScopeLevel
import           AST.Term.Apply
import           AST.Term.Scheme
import           AST.Term.Scope
import           AST.Term.Scope.InvDeBruijn
import           AST.Term.TypeSig
import           AST.Unify
import           AST.Unify.PureBinding
import           AST.Unify.STBinding
import           Control.Applicative
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Constraint
import           Data.Proxy (Proxy(..))
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

data LangA v k
    = ALam (Scope LangA v k)
    | AVar (ScopeVar LangA v k)
    | AApp (Apply (LangA v) k)
    | ATypeSig (TypeSig (Tree Pure (Scheme Types Typ)) (LangA v) k)
    | ALit Int

makeChildrenRecursive [''LangA]
instance Recursive Children (LangA v)

type instance TypeOf (LangA k) = Typ
type instance ScopeOf (LangA k) = ScopeTypes Typ

instance InvDeBruijnIndex v => Pretty (LangA v ('Knot Pure)) where
    pPrintPrec lvl p (ALam (Scope expr)) =
        Pretty.hcat
        [ Pretty.text "λ("
        , pPrint (1 + deBruijnIndexMax (Proxy :: Proxy v))
        , Pretty.text ")."
        ] <+> pPrintPrec lvl 0 expr
        & maybeParens (p > 0)
    pPrintPrec _ _ (AVar (ScopeVar v)) =
        Pretty.text "#" <> pPrint (inverseDeBruijnIndex # v)
    pPrintPrec lvl p (AApp (Apply f x)) =
        pPrintPrec lvl p f <+> pPrintPrec lvl p x
    pPrintPrec lvl p (ATypeSig typeSig) = pPrintPrec lvl p typeSig
    pPrintPrec _ _ (ALit i) = pPrint i

instance HasTypeOf1 LangA where
    type TypeOf1 LangA = Typ
    type TypeOfIndexConstraint LangA = DeBruijnIndex
    typeAst _ = Dict

type TermInfer1Deps env m =
    ( MonadScopeLevel m
    , MonadReader env m
    , HasScopeTypes (UVar m) Typ env
    , HasScope m (ScopeTypes Typ)
    , Unify m Typ, Unify m Row
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

newtype PureInferA a =
    PureInferA
    ( RWST (Tree (ScopeTypes Typ) (Const Int), ScopeLevel) () PureInferState
        (Either (Tree TypeError Pure)) a
    )
    deriving
    ( Functor, Applicative, Monad
    , MonadError (Tree TypeError Pure)
    , MonadReader (Tree (ScopeTypes Typ) (Const Int), ScopeLevel)
    , MonadState PureInferState
    )

type instance UVar PureInferA = Const Int

instance HasScope PureInferA (ScopeTypes Typ) where
    getScope = Lens.view Lens._1

instance MonadScopeLevel PureInferA where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify PureInferA Typ where
    binding = pureBinding (Lens._1 . tTyp)
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> Name . ('t':) . show
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify PureInferA))) applyBindings e
        >>= throwError . TypError

instance Unify PureInferA Row where
    binding = pureBinding (Lens._1 . tRow)
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> Name . ('r':) . show
    structureMismatch = rStructureMismatch
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify PureInferA))) applyBindings e
        >>= throwError . RowError

newtype STInferA s a =
    STInferA
    ( ReaderT (Tree (ScopeTypes Typ) (STVar s), ScopeLevel, STInferState s)
        (ExceptT (Tree TypeError Pure) (ST s)) a
    )
    deriving
    ( Functor, Applicative, Monad, MonadST
    , MonadError (Tree TypeError Pure)
    , MonadReader (Tree (ScopeTypes Typ) (STVar s), ScopeLevel, STInferState s)
    )

type instance UVar (STInferA s) = STVar s

instance HasScope (STInferA s) (ScopeTypes Typ) where
    getScope = Lens.view Lens._1

instance MonadScopeLevel (STInferA s) where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify (STInferA s) Typ where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tTyp) <&> Name . ('t':) . show
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify (STInferA s)))) applyBindings e
        >>= throwError . TypError

instance Unify (STInferA s) Row where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tRow) <&> Name . ('r':) . show
    structureMismatch = rStructureMismatch
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify (STInferA s)))) applyBindings e
        >>= throwError . RowError
