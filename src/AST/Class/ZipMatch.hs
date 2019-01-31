{-# LANGUAGE NoImplicitPrelude, RankNTypes, ConstraintKinds, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds, TemplateHaskell #-}

module AST.Class.ZipMatch
    ( ZipMatch(..), Both(..), bothA, bothB
    , zipMatchWith, zipMatchWithA, zipMatchWith_
    , doesMatch
    ) where

import           AST.Class.Children (Children(..))
import           AST.Class.Children.TH (makeChildren)
import           AST.Knot (Knot, Tree)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard)
import           Data.Functor.Const (Const(..))
import           Data.Functor.Identity (Identity(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data Both a b (k :: Knot) = Both
    { _bothA :: a k
    , _bothB :: b k
    } deriving (Eq, Ord, Show)
Lens.makeLenses ''Both

makeChildren ''Both

class Children expr => ZipMatch expr where
    zipMatch :: Tree expr a -> Tree expr b -> Maybe (Tree expr (Both a b))

instance (ZipMatch a, ZipMatch b) => ZipMatch (Both a b) where
    {-# INLINE zipMatch #-}
    zipMatch (Both a0 b0) (Both a1 b1) = Both <$> zipMatch a0 a1 <*> zipMatch b0 b1

instance Eq a => ZipMatch (Const a) where
    {-# INLINE zipMatch #-}
    zipMatch (Const x) (Const y) = Const x <$ guard (x == y)

{-# INLINE zipMatchWithA #-}
zipMatchWithA ::
    forall expr f constraint a b c.
    (ZipMatch expr, Applicative f, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> f (Tree c child)) ->
    Tree expr a -> Tree expr b -> Maybe (f (Tree expr c))
zipMatchWithA p f x y =
    zipMatch x y <&> children p g
    where
        g :: constraint child => Tree (Both a b) child -> f (Tree c child)
        g (Both a b) = f a b

{-# INLINE zipMatchWith #-}
zipMatchWith ::
    (ZipMatch expr, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> Tree c child) ->
    Tree expr a -> Tree expr b -> Maybe (Tree expr c)
zipMatchWith p f x y = zipMatchWithA p (fmap Identity . f) x y <&> runIdentity

{-# INLINE zipMatchWith_ #-}
zipMatchWith_ ::
    forall f expr constraint a b.
    (Applicative f, ZipMatch expr, ChildrenConstraint expr constraint) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> f ()) ->
    Tree expr a -> Tree expr b -> Maybe (f ())
zipMatchWith_ p f x y =
    ( zipMatchWithA p (f <&> Lens.mapped . Lens.mapped .~ Const ()) x y
        :: Maybe (f (Tree expr (Const ())))
    ) <&> Lens.mapped .~ ()

{-# INLINE doesMatch #-}
doesMatch :: ZipMatch expr => Tree expr a -> Tree expr b -> Bool
doesMatch x y = Lens.has Lens._Just (zipMatch x y)
