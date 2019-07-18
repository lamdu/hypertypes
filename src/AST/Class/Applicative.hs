{-# LANGUAGE NoImplicitPrelude, RankNTypes #-}

module AST.Class.Applicative
    ( KApplicative(..)
    ) where

import AST.Class.Functor (KFunctor)
import AST.Class.Pointed (KPointed)
import AST.Knot (Tree)

class (KPointed k, KFunctor k) => KApplicative k where
    liftK2 ::
        (forall child. Tree l child -> Tree m child -> Tree n child) ->
        Tree k l -> Tree k m -> Tree k n
