{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, LambdaCase, MultiParamTypeClasses, DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances, DataKinds, ConstraintKinds, RankNTypes #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}

-- | A test language with locally-nameless variable scoping and type signatures with for-alls

module LangA where

import           TypeLang

import           AST
import           AST.Class.Infer.Infer1
import           AST.Class.Unify
import           AST.Combinator.Pair
import           AST.Infer
import           AST.Term.Apply
import           AST.Term.NamelessScope
import           AST.Term.NamelessScope.InvDeBruijn
import           AST.Term.TypeSig
import           AST.Unify
import           AST.Unify.Apply
import           AST.Unify.Binding
import           AST.Unify.Binding.ST
import           AST.Unify.New
import           AST.Unify.QuantifiedVar
import           Control.Applicative
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Except
import           Control.Monad.RWS
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.ST.Class (MonadST(..))
import           Data.Constraint
import           Data.Proxy (Proxy(..))
import           Data.STRef
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

data LangA v k
    = ALam (Scope LangA v k)
    | AVar (ScopeVar LangA v k)
    | AApp (Apply (LangA v) k)
    | ATypeSig (TypeSig Types (LangA v) k)
    | ALit Int

instance HasNodes (LangA v) where
    type NodeTypesOf (LangA v) = Pair (LangA v) (LangA (Maybe v))
    type NodesConstraint (LangA v) = KnotsConstraint '[LangA v, LangA (Maybe v)]

makeKTraversableAndBases ''LangA
instance Recursively HasNodes (LangA v)

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
    , HasScopeTypes (UVarOf m) Typ env
    , HasScope m (ScopeTypes Typ)
    , Unify m Typ, Unify m Row
    )

instance TermInfer1Deps env m => Infer1 m LangA where
    inferMonad = Sub Dict

instance (DeBruijnIndex k, TermInfer1Deps env m) => Infer m (LangA k) where
    inferBody (ALit     x) = newTerm TInt <&> InferRes (ALit x)
    inferBody (AVar     x) = inferBody x <&> inferResBody %~ AVar
    inferBody (ALam     x) = inferBody x <&> inferResBody %~ ALam
    inferBody (AApp     x) = inferBody x <&> inferResBody %~ AApp
    inferBody (ATypeSig x) = inferBody x <&> inferResBody %~ ATypeSig

instance (DeBruijnIndex k, TermInfer1Deps env m) => Recursively (Infer m) (LangA k)

instance (c Typ, c Row) => Recursively (InferChildConstraints c) (LangA k)

-- Monads for inferring `LangA`:

newtype PureInferA a =
    PureInferA
    ( RWST (Tree (ScopeTypes Typ) UVar, ScopeLevel) () PureInferState
        (Either (Tree TypeError Pure)) a
    )
    deriving newtype
    ( Functor, Applicative, Monad
    , MonadError (Tree TypeError Pure)
    , MonadReader (Tree (ScopeTypes Typ) UVar, ScopeLevel)
    , MonadState PureInferState
    )

execPureInferA :: PureInferA a -> Either (Tree TypeError Pure) a
execPureInferA (PureInferA act) =
    runRWST act (mempty, ScopeLevel 0) emptyPureInferState <&> (^. Lens._1)

type instance UVarOf PureInferA = UVar

instance HasScope PureInferA (ScopeTypes Typ) where
    getScope = Lens.view Lens._1

instance MonadScopeLevel PureInferA where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance MonadScopeConstraints ScopeLevel PureInferA where
    scopeConstraints = Lens.view Lens._2

instance MonadScopeConstraints RConstraints PureInferA where
    scopeConstraints = Lens.view Lens._2 <&> RowConstraints mempty

instance MonadQuantify ScopeLevel Name PureInferA where
    newQuantifiedVariable _ =
        Lens._2 . tTyp . _UVar <<+= 1 <&> Name . ('t':) . show

instance MonadQuantify RConstraints Name PureInferA where
    newQuantifiedVariable _ =
        Lens._2 . tRow . _UVar <<+= 1 <&> Name . ('r':) . show

instance Unify PureInferA Typ where
    binding = bindingDict (Lens._1 . tTyp)
    unifyError e =
        traverseKWith (Proxy :: Proxy '[Recursively (Unify PureInferA)]) applyBindings e
        >>= throwError . TypError

instance Unify PureInferA Row where
    binding = bindingDict (Lens._1 . tRow)
    structureMismatch = rStructureMismatch
    unifyError e =
        traverseKWith (Proxy :: Proxy '[Recursively (Unify PureInferA)]) applyBindings e
        >>= throwError . RowError

newtype STInferA s a =
    STInferA
    ( ReaderT (Tree (ScopeTypes Typ) (STUVar s), ScopeLevel, STNameGen s)
        (ExceptT (Tree TypeError Pure) (ST s)) a
    )
    deriving newtype
    ( Functor, Applicative, Monad, MonadST
    , MonadError (Tree TypeError Pure)
    , MonadReader (Tree (ScopeTypes Typ) (STUVar s), ScopeLevel, STNameGen s)
    )

execSTInferA :: STInferA s a -> ST s (Either (Tree TypeError Pure) a)
execSTInferA (STInferA act) =
    do
        qvarGen <- Types <$> (newSTRef 0 <&> Const) <*> (newSTRef 0 <&> Const)
        runReaderT act (mempty, ScopeLevel 0, qvarGen) & runExceptT

type instance UVarOf (STInferA s) = STUVar s

instance HasScope (STInferA s) (ScopeTypes Typ) where
    getScope = Lens.view Lens._1

instance MonadScopeLevel (STInferA s) where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance MonadScopeConstraints ScopeLevel (STInferA s) where
    scopeConstraints = Lens.view Lens._2

instance MonadScopeConstraints RConstraints (STInferA s) where
    scopeConstraints = Lens.view Lens._2 <&> RowConstraints mempty

instance MonadQuantify ScopeLevel Name (STInferA s) where
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tTyp) <&> Name . ('t':) . show

instance MonadQuantify RConstraints Name (STInferA s) where
    newQuantifiedVariable _ = newStQuantified (Lens._3 . tRow) <&> Name . ('r':) . show

instance Unify (STInferA s) Typ where
    binding = stBinding
    unifyError e =
        traverseKWith (Proxy :: Proxy '[Recursively (Unify (STInferA s))]) applyBindings e
        >>= throwError . TypError

instance Unify (STInferA s) Row where
    binding = stBinding
    structureMismatch = rStructureMismatch
    unifyError e =
        traverseKWith (Proxy :: Proxy '[Recursively (Unify (STInferA s))]) applyBindings e
        >>= throwError . RowError
