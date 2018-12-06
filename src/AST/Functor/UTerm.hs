{-# LANGUAGE NoImplicitPrelude, DeriveTraversable, TemplateHaskell #-}

module AST.Functor.UTerm
    ( UTerm(..), _UVar, _UTerm
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators

import           Prelude.Compat

-- Names modeled after unification-fd

data UTerm f a
    = UVar (f a)
    | UTerm a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
Lens.makePrisms ''UTerm

-- TODO:
-- Are there any compelling use cases for UTerm's Applicative and Monad instances?
-- Will `f` even ever be an Applicative or Monad?
-- Defined those for completeness as these are the
-- only possible instances for these classses iiuc.

instance Applicative f => Applicative (UTerm f) where
    pure = UTerm
    UTerm f <*> UTerm x = UTerm (f x)
    UTerm f <*> UVar x = UVar (x <&> f)
    UVar f <*> UTerm x = UVar (f ?? x)
    UVar f <*> UVar x = UVar (f <*> x)

instance Monad f => Monad (UTerm f) where
    UTerm x >>= f = f x
    UVar x >>= f =
        UVar (x >>= u . f)
        where
            u (UVar v) = v
            u (UTerm t) = pure t
