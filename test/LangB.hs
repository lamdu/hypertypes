{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, TypeFamilies, LambdaCase #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, TupleSections #-}
{-# LANGUAGE ScopedTypeVariables, GeneralizedNewtypeDeriving, DataKinds #-}

module LangB where

import           TypeLang

import           AST
import           AST.Class.Infer
import           AST.Class.Infer.ScopeLevel
import           AST.Class.Instantiate
import           AST.Term.Apply
import           AST.Term.Lam
import           AST.Term.Let
import           AST.Term.RowExtend
import           AST.Term.Var
import           AST.Unify
import           AST.Unify.Generalize
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
import           Data.Map (Map)
import           Data.Maybe
import           Data.Proxy
import           Text.PrettyPrint ((<+>))
import qualified Text.PrettyPrint as Pretty
import           Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

data LangB k
    = BLit Int
    | BApp (Apply LangB k)
    | BVar (Var Name LangB k)
    | BLam (Lam Name LangB k)
    | BLet (Let Name LangB k)
    | BRecEmpty
    | BRecExtend (RowExtend Name LangB LangB k)

makeChildrenRecursive [''LangB]

type instance TypeOf LangB = Typ

instance Pretty (Tree LangB Pure) where
    pPrintPrec _ _ (BLit i) = pPrint i
    pPrintPrec _ _ BRecEmpty = Pretty.text "{}"
    pPrintPrec lvl p (BRecExtend (RowExtend k v r)) =
        pPrintPrec lvl 20 k <+>
        Pretty.text "=" <+>
        (pPrintPrec lvl 2 v <> Pretty.text ",") <+>
        pPrintPrec lvl 1 r
        & maybeParens (p > 1)
    pPrintPrec lvl p (BApp x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BVar x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BLam x) = pPrintPrec lvl p x
    pPrintPrec lvl p (BLet x) = pPrintPrec lvl p x

instance
    ( MonadScopeLevel m
    , MonadScopeTypes Name Typ m
    , LocalScopeType Name (Tree (UVar m) Typ) m
    , LocalScopeType Name (Tree (GTerm (UVar m)) Typ) m
    , Recursive (Unify m) Typ
    ) =>
    Infer m LangB where

    infer (BApp x) = infer x <&> _2 %~ BApp
    infer (BVar x) = infer x <&> _2 %~ BVar
    infer (BLam x) = infer x <&> _2 %~ BLam
    infer (BLet x) = infer x <&> _2 %~ BLet
    infer (BLit x) = newTerm TInt <&> (, BLit x)
    infer (BRecExtend x) =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        do
            (xT, xI) <- inferRowExtend TRec RExtend x
            TRec xT & newTerm <&> (, BRecExtend xI)
    infer BRecEmpty =
        withDict (recursive :: RecursiveDict (Unify m) Typ) $
        newTerm REmpty >>= newTerm . TRec <&> (, BRecEmpty)

-- Monads for inferring `LangB`:

newtype ScopeTypes v = ScopeTypes (Map Name (Either (Tree v Typ) (Tree (GTerm v) Typ)))
    deriving (Semigroup, Monoid)
Lens.makePrisms ''ScopeTypes

newtype PureInferB a =
    PureInferB
    ( RWST (ScopeTypes (Const Int), ScopeLevel) () PureInferState
        (Either (Tree TypeError Pure)) a
    )
    deriving
    ( Functor, Applicative, Monad
    , MonadError (Tree TypeError Pure)
    , MonadReader (ScopeTypes (Const Int), ScopeLevel)
    , MonadState PureInferState
    )

type instance UVar PureInferB = Const Int

instance MonadScopeTypes Name Typ PureInferB where
    scopeType v =
        Lens.view (Lens._1 . _ScopeTypes . Lens.at v)
        <&> fromMaybe (error "name error")
        >>= either pure instantiate

instance LocalScopeType Name (Tree (Const Int) Typ) PureInferB where
    localScopeType k v = local (Lens._1 . _ScopeTypes . Lens.at k ?~ Left v)

instance LocalScopeType Name (Tree (GTerm (Const Int)) Typ) PureInferB where
    localScopeType k v = local (Lens._1 . _ScopeTypes . Lens.at k ?~ Right v)

instance MonadScopeLevel PureInferB where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify PureInferB Typ where
    binding = pureBinding (Lens._1 . tTyp)
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> Name . ('t':) . show
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify PureInferB))) applyBindings e
        >>= throwError . TypError

instance Unify PureInferB Row where
    binding = pureBinding (Lens._1 . tRow)
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> Name . ('r':) . show
    structureMismatch = rStructureMismatch
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify PureInferB))) applyBindings e
        >>= throwError . RowError

instance Recursive (Unify PureInferB) Typ
instance Recursive (Unify PureInferB) Row

newtype STInferB s a =
    STInferB
    (ReaderT (ScopeTypes (STVar s), ScopeLevel, STInferState s)
        (ExceptT (Tree TypeError Pure) (ST s)) a
    )
    deriving
    ( Functor, Applicative, Monad, MonadST
    , MonadError (Tree TypeError Pure)
    , MonadReader (ScopeTypes (STVar s), ScopeLevel, STInferState s)
    )

type instance UVar (STInferB s) = STVar s

instance MonadScopeTypes Name Typ (STInferB s) where
    scopeType v =
        Lens.view (Lens._1 . _ScopeTypes . Lens.at v)
        <&> fromMaybe (error "name error")
        >>= either pure instantiate

instance LocalScopeType Name (Tree (STVar s) Typ) (STInferB s) where
    localScopeType k v = local (Lens._1 . _ScopeTypes . Lens.at k ?~ Left v)

instance LocalScopeType Name (Tree (GTerm (STVar s)) Typ) (STInferB s) where
    localScopeType k v = local (Lens._1 . _ScopeTypes . Lens.at k ?~ Right v)

instance MonadScopeLevel (STInferB s) where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify (STInferB s) Typ where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tTyp) <&> Name . ('t':) . show
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify (STInferB s)))) applyBindings e
        >>= throwError . TypError

instance Unify (STInferB s) Row where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tRow) <&> Name . ('r':) . show
    structureMismatch = rStructureMismatch
    unifyError e =
        children (Proxy :: Proxy (Recursive (Unify (STInferB s)))) applyBindings e
        >>= throwError . RowError

instance Recursive (Unify (STInferB s)) Typ
instance Recursive (Unify (STInferB s)) Row
