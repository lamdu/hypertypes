{-# LANGUAGE NoImplicitPrelude, RankNTypes, ConstraintKinds, ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts, TypeApplications #-}

module AST.Class.ZipMatch
    ( ZipMatch(..)
    , zipMatchWith, zipMatchWithA, zipMatchWith_
    , doesMatch
    , Both(..)
    ) where

import           AST.Class.Combinators
import           AST.Class.Foldable (KFoldable)
import           AST.Class.Functor (KFunctor)
import           AST.Class.Traversable (KTraversable)
import           AST.Combinator.Both (Both(..))
import           AST.Knot (Tree, NodeTypesOf)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard)
import           Data.Foldable (sequenceA_)
import           Data.Functor.Const (Const(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

class ZipMatch expr where
    zipMatch :: Tree expr a -> Tree expr b -> Maybe (Tree expr (Both a b))

instance (ZipMatch a, ZipMatch b) => ZipMatch (Both a b) where
    {-# INLINE zipMatch #-}
    zipMatch (Both a0 b0) (Both a1 b1) = Both <$> zipMatch a0 a1 <*> zipMatch b0 b1

instance Eq a => ZipMatch (Const a) where
    {-# INLINE zipMatch #-}
    zipMatch (Const x) (Const y) = Const x <$ guard (x == y)

{-# INLINE zipMatchWithA #-}
zipMatchWithA ::
    forall expr f constraints a b c.
    ( Applicative f
    , ZipMatch expr, KTraversable expr
    , KLiftConstraints constraints (NodeTypesOf expr)
    ) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree a child -> Tree b child -> f (Tree c child)) ->
    Tree expr a -> Tree expr b -> Maybe (f (Tree expr c))
zipMatchWithA p f x y = zipMatch x y <&> traverseKWith p (\(Both a b) -> f a b)

{-# INLINE zipMatchWith #-}
zipMatchWith ::
    ( ZipMatch expr, KFunctor expr
    , KLiftConstraints constraints (NodeTypesOf expr)
    ) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree a child -> Tree b child -> Tree c child) ->
    Tree expr a -> Tree expr b -> Maybe (Tree expr c)
zipMatchWith p f x y = zipMatch x y <&> mapKWith p (\(Both a b) -> f a b)

{-# INLINE zipMatchWith_ #-}
zipMatchWith_ ::
    forall f expr constraints a b.
    ( Applicative f
    , ZipMatch expr, KFoldable expr
    , KLiftConstraints constraints (NodeTypesOf expr)
    ) =>
    Proxy constraints ->
    (forall child. ApplyKConstraints constraints child => Tree a child -> Tree b child -> f ()) ->
    Tree expr a -> Tree expr b -> Maybe (f ())
zipMatchWith_ p f x y =
    zipMatch x y
    <&> sequenceA_ . foldMapKWith @[f ()] p (\(Both a b) -> [f a b])

{-# INLINE doesMatch #-}
doesMatch :: ZipMatch expr => Tree expr a -> Tree expr b -> Bool
doesMatch x y = Lens.has Lens._Just (zipMatch x y)
