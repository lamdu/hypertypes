{-# LANGUAGE RankNTypes #-}
-- | Pure combinators for LangA

module LangA.Pure
    ( module LangA
    , module LangA.Pure
    ) where

import AST
import AST.Term.Apply
import AST.Term.Scheme
import AST.Term.Scope.InvDeBruijn
import AST.Term.TypeSig
import Control.Lens.Operators
import LangA
import TypeLang

aLam ::
    InvDeBruijnIndex t =>
    ((forall n. InvDeBruijnIndex n =>
        Tree Pure (LangA n)) -> Tree Pure (LangA (Maybe t))) ->
    Tree Pure (LangA t)
aLam f = (Pure . ALam . scope) (\x -> f (var x))

($::) :: Tree Pure (LangA n) -> Tree Pure (Scheme Types Typ) -> Tree Pure (LangA n)
v $:: t = v `TypeSig` t & ATypeSig & Pure

aLit :: Int -> Tree Pure (LangA t)
aLit = Pure . ALit

aApp :: Tree Pure (LangA n) -> Tree Pure (LangA n) -> Tree Pure (LangA n)
f `aApp` x = Apply f x & AApp & Pure

var :: InvDeBruijnIndex k => Int -> Tree Pure (LangA k)
var = Pure . AVar . scopeVar
