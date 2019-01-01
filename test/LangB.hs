{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, TypeFamilies #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances, TupleSections #-}
{-# LANGUAGE ScopedTypeVariables, GeneralizedNewtypeDeriving, DataKinds #-}

module LangB where

import TypeLang

import AST
import AST.Class.Infer
import AST.Class.Infer.ScopeLevel
import AST.Unify
import AST.Term.Apply
import AST.Term.Lam
import AST.Term.Let
import AST.Term.RowExtend
import AST.Term.Var
import AST.Unify.PureBinding
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
import Data.Map (Map)
import Data.Maybe

data LangB k
    = BLit Int
    | BApp (Apply LangB k)
    | BVar (Var String LangB k)
    | BLam (Lam String LangB k)
    | BLet (Let String LangB k)
    | BRecEmpty
    | BRecExtend (RowExtend String LangB LangB k)

makeChildrenRecursive [''LangB]

type instance TypeAST LangB = Typ

instance (MonadScopeLevel m, MonadScopeTypes [Char] Typ m, Recursive (Unify m) Typ) => Infer m LangB where
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

newtype IntInferB a =
    IntInferB (RWST (Map String (IntInferB (Tree (Const Int) Typ)), ScopeLevel) () IntInferState Maybe a)
    deriving
    ( Functor, Applicative, Alternative, Monad
    , MonadReader (Map String (IntInferB (Tree (Const Int) Typ)), ScopeLevel)
    , MonadState IntInferState
    )

type instance UVar IntInferB = Const Int

instance MonadScopeTypes String Typ IntInferB where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadScopeLevel IntInferB where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify IntInferB Typ where
    binding = pureBinding (Lens._1 . tTyp)
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Unify IntInferB Row where
    binding = pureBinding (Lens._1 . tRow)
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show
    structureMismatch = rStructureMismatch

instance Recursive (Unify IntInferB) Typ
instance Recursive (Unify IntInferB) Row

newtype STInferB s a =
    STInferB
    (ReaderT (Map String (STInferB s (Tree (STVar s) Typ)), ScopeLevel, STInferState s) (MaybeT (ST s)) a)
    deriving
    ( Functor, Applicative, Alternative, Monad, MonadST
    , MonadReader (Map String (STInferB s (Tree (STVar s) Typ)), ScopeLevel, STInferState s)
    )

type instance UVar (STInferB s) = STVar s

instance MonadScopeTypes String Typ (STInferB s) where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadScopeLevel (STInferB s) where
    localLevel = local (Lens._2 . _ScopeLevel +~ 1)

instance Unify (STInferB s) Typ where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tTyp) <&> ('t':) . show

instance Unify (STInferB s) Row where
    binding = stBindingState
    scopeConstraints _ = Lens.view Lens._2 <&> RowConstraints mempty
    newQuantifiedVariable _ _ = newStQuantified (Lens._3 . tRow) <&> ('r':) . show
    structureMismatch = rStructureMismatch

instance Recursive (Unify (STInferB s)) Typ
instance Recursive (Unify (STInferB s)) Row
