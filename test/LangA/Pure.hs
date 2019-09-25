-- | Pure combinators for LangA

module LangA.Pure
    ( module LangA
    , module LangA.Pure
    ) where

import Hyper
import Hyper.Type.AST.App
import Hyper.Type.AST.NamelessScope.InvDeBruijn
import Hyper.Type.AST.Scheme
import Hyper.Type.AST.TypeSig
import LangA
import TypeLang

import Prelude

aLam ::
    InvDeBruijnIndex t =>
    ((forall n. InvDeBruijnIndex n =>
        Tree Pure (LangA n)) -> Tree Pure (LangA (Maybe t))) ->
    Tree Pure (LangA t)
aLam f =
    scope body &# ALam
    where
        body x = f (var x)

($::) :: Tree Pure (LangA n) -> Tree Pure (Scheme Types Typ) -> Tree Pure (LangA n)
v $:: t = v `TypeSig` t &# ATypeSig

aApp :: Tree Pure (LangA n) -> Tree Pure (LangA n) -> Tree Pure (LangA n)
f `aApp` x = App f x &# AApp

var :: InvDeBruijnIndex h => Int -> Tree Pure (LangA h)
var i = scopeVar i &# AVar
