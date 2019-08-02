{-# LANGUAGE RankNTypes #-}
-- | Pure combinators for LangA

module LangA.Pure
    ( module LangA
    , module LangA.Pure
    ) where

import AST
import AST.Term.App
import AST.Term.NamelessScope.InvDeBruijn
import AST.Term.Scheme
import AST.Term.TypeSig
import Control.Lens.Operators
import LangA
import TypeLang

import Prelude

aLam ::
    InvDeBruijnIndex t =>
    ((forall n. InvDeBruijnIndex n =>
        Tree Pure (LangA n)) -> Tree Pure (LangA (Maybe t))) ->
    Tree Pure (LangA t)
aLam f =
    _Pure # ALam (scope body)
    where
        body x = f (var x)

($::) :: Tree Pure (LangA n) -> Tree Pure (Scheme Types Typ) -> Tree Pure (LangA n)
v $:: t = _Pure # ATypeSig (v `TypeSig` t)

aLit :: Int -> Tree Pure (LangA t)
aLit i = _Pure # ALit i

aApp :: Tree Pure (LangA n) -> Tree Pure (LangA n) -> Tree Pure (LangA n)
f `aApp` x = _Pure # AApp (App f x)

var :: InvDeBruijnIndex k => Int -> Tree Pure (LangA k)
var i = _Pure # AVar (scopeVar i)
