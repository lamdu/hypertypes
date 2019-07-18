{-# LANGUAGE NoImplicitPrelude, RankNTypes #-}

module AST.Class.Applicative
    ( KApplicative(..)
    , liftK1
    ) where

import AST.Class.Pointed (KPointed)
import AST.Knot (Tree)

import Prelude.Compat

class KPointed k => KApplicative k where
    liftK2 ::
        (forall child. Tree l child -> Tree m child -> Tree n child) ->
        Tree k l -> Tree k m -> Tree k n

liftK1 ::
    KApplicative k =>
    (forall child. Tree m child -> Tree n child) ->
    Tree k m -> Tree k n
liftK1 f x = liftK2 (const . f) x x
