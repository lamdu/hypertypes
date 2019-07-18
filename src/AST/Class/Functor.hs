{-# LANGUAGE NoImplicitPrelude, RankNTypes #-}

module AST.Class.Functor
    ( KFunctor(..)
    ) where

import AST.Knot (Tree)

class KFunctor k where
    mapK ::
        (forall child. Tree m child -> Tree n child) ->
        Tree k m -> Tree k n
