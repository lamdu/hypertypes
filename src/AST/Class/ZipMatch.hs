{-# LANGUAGE RankNTypes, DefaultSignatures #-}

module AST.Class.ZipMatch
    ( ZipMatch(..), RZipMatch
    , zipMatchWith, zipMatchWithA, zipMatchWith_, zipMatch1_
    ) where

import           AST.Class.Foldable
import           AST.Class.Functor (KFunctor(..))
import           AST.Class.Nodes (KNodes(..))
import           AST.Class.Recursive (Recursive(..), RNodes)
import           AST.Class.Traversable (KTraversable, traverseKWith)
import           AST.Knot (Tree)
import           AST.Knot.Pure (Pure(..), _Pure)
import           Control.Lens.Operators
import           Control.Monad (guard)
import           Data.Constraint (Dict(..))
import           Data.Functor.Const (Const(..))
import           Data.Functor.Product.PolyKinds (Product(..))
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

-- | A class to match term structures.
--
-- Similar to a partial version of 'AST.Class.Apply.Apply' but the semantics are different -
-- when the terms contain plain values, 'AST.Class.Apply.zipK' would append them,
-- but 'zipMatch' would compare them and only produce a result if they match.
--
-- The `TemplateHaskell` generators 'AST.TH.Apply.makeKApply' and 'AST.TH.ZipMatch.makeZipMatch'
-- create the instances according to these semantics.
class ZipMatch expr where
    -- | Compare two structures
    --
    -- >>> zipMatch (NewPerson p0) (NewPerson p1)
    -- Just (NewPerson (Pair p0 p1))
    -- >>> zipMatch (NewPerson p) (NewCake c)
    -- Nothing
    zipMatch :: Tree expr a -> Tree expr b -> Maybe (Tree expr (Product a b))

instance (ZipMatch a, ZipMatch b) => ZipMatch (Product a b) where
    {-# INLINE zipMatch #-}
    zipMatch (Pair a0 b0) (Pair a1 b1) = Pair <$> zipMatch a0 a1 <*> zipMatch b0 b1

instance ZipMatch Pure where
    {-# INLINE zipMatch #-}
    zipMatch (Pure x) (Pure y) = _Pure # Pair x y & Just

instance Eq a => ZipMatch (Const a) where
    {-# INLINE zipMatch #-}
    zipMatch (Const x) (Const y) = Const x <$ guard (x == y)

-- | A class of 'AST.Knot.Knot's which recursively implement 'ZipMatch'.
--
-- Can be used with the combinators in "AST.Class.Recursive".
class (ZipMatch k, RNodes k) => RZipMatch k where
    recursiveZipMatch :: Proxy k -> Dict (NodesConstraint k RZipMatch)
    {-# INLINE recursiveZipMatch #-}
    default recursiveZipMatch ::
        NodesConstraint k RZipMatch =>
        Proxy k -> Dict (NodesConstraint k RZipMatch)
    recursiveZipMatch _ = Dict

instance RZipMatch Pure
instance Eq a => RZipMatch (Const a)

instance Recursive RZipMatch where
    {-# INLINE recurse #-}
    recurse = recursiveZipMatch . (const Proxy :: Proxy (RZipMatch k) -> Proxy k)

-- | 'ZipMatch' variant of 'Control.Applicative.liftA2'
{-# INLINE zipMatchWith #-}
zipMatchWith ::
    ( ZipMatch expr, KFunctor expr
    , NodesConstraint expr constraint
    ) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> Tree c child) ->
    Tree expr a -> Tree expr b -> Maybe (Tree expr c)
zipMatchWith p f x y = zipMatch x y <&> mapKWith p (\(Pair a b) -> f a b)

-- | An 'Applicative' variant of 'zipMatchWith'
{-# INLINE zipMatchWithA #-}
zipMatchWithA ::
    forall expr f constraint a b c.
    ( Applicative f
    , ZipMatch expr, KTraversable expr
    , NodesConstraint expr constraint
    ) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> f (Tree c child)) ->
    Tree expr a -> Tree expr b -> Maybe (f (Tree expr c))
zipMatchWithA p f x y = zipMatch x y <&> traverseKWith p (\(Pair a b) -> f a b)

-- | A variant of 'zipMatchWithA' where the 'Applicative' actions do not contain results
{-# INLINE zipMatchWith_ #-}
zipMatchWith_ ::
    forall f expr constraint a b.
    ( Applicative f
    , ZipMatch expr, KFoldable expr
    , NodesConstraint expr constraint
    ) =>
    Proxy constraint ->
    (forall child. constraint child => Tree a child -> Tree b child -> f ()) ->
    Tree expr a -> Tree expr b -> Maybe (f ())
zipMatchWith_ p f x y = zipMatch x y <&> traverseKWith_ p (\(Pair a b) -> f a b)

-- | A variant of 'zipMatchWith_' for 'Knot's with a single node type (avoids using `RankNTypes`)
{-# INLINE zipMatch1_ #-}
zipMatch1_ ::
    ( Applicative f
    , ZipMatch k, KFoldable k
    , NodesConstraint k ((~) c)
    ) =>
    (Tree a c -> Tree b c -> f ()) ->
    Tree k a -> Tree k b -> Maybe (f ())
zipMatch1_ f x y = zipMatch x y <&> traverseK1_ (\(Pair a b) -> f a b)
