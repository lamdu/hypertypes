{-# LANGUAGE ScopedTypeVariables #-}

module AST.Term.NamelessScope.InvDeBruijn
    ( InvDeBruijnIndex(..), inverseDeBruijnIndex, scope, scopeVar
    ) where

import AST.Knot (Tree)
import AST.Term.NamelessScope (DeBruijnIndex(..), EmptyScope, Scope(..), ScopeVar(..))
import Control.Lens (Prism', iso)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))

import Prelude.Compat

class DeBruijnIndex a => InvDeBruijnIndex a where
    deBruijnIndexMax :: Proxy a -> Int

instance InvDeBruijnIndex EmptyScope where
    deBruijnIndexMax _ = -1

instance InvDeBruijnIndex a => InvDeBruijnIndex (Maybe a) where
    deBruijnIndexMax _ = 1 + deBruijnIndexMax (Proxy @a)

inverseDeBruijnIndex :: forall a. InvDeBruijnIndex a => Prism' Int a
inverseDeBruijnIndex =
    iso (l -) (l -) . deBruijnIndex
    where
        l = deBruijnIndexMax (Proxy @a)

scope ::
    forall expr a f.
    InvDeBruijnIndex a =>
    (Int -> Tree f (expr (Maybe a))) ->
    Tree (Scope expr a) f
scope f = Scope (f (inverseDeBruijnIndex # (Nothing :: Maybe a)))

scopeVar :: InvDeBruijnIndex a => Int -> ScopeVar expr a f
scopeVar x = ScopeVar (x ^?! inverseDeBruijnIndex)
