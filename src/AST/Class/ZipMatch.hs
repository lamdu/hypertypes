{-# LANGUAGE RankNTypes, DefaultSignatures #-}

module AST.Class.ZipMatch
    ( ZipMatch(..), RZipMatch
    , zipMatch2, zipMatch2With
    , zipMatchA, zipMatchWithA
    , zipMatch_, zipMatchWith_, zipMatch1_
    ) where

import           AST.Class.Foldable
import           AST.Class.Functor (KFunctor(..), mapKWith)
import           AST.Class.Nodes (KNodes(..))
import           AST.Class.Recursive (Recursive(..), RNodes)
import           AST.Class.Traversable (KTraversable, traverseK, traverseKWith)
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
-- The @TemplateHaskell@ generators 'AST.TH.Apply.makeKApply' and 'AST.TH.ZipMatch.makeZipMatch'
-- create the instances according to these semantics.
class ZipMatch k where
    -- | Compare two structures
    --
    -- >>> zipMatch (NewPerson p0) (NewPerson p1)
    -- Just (NewPerson (Pair p0 p1))
    -- >>> zipMatch (NewPerson p) (NewCake c)
    -- Nothing
    zipMatch :: Tree k p -> Tree k q -> Maybe (Tree k (Product p q))

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
    recursiveZipMatch :: Proxy k -> Dict (KNodesConstraint k RZipMatch)
    {-# INLINE recursiveZipMatch #-}
    default recursiveZipMatch ::
        KNodesConstraint k RZipMatch =>
        Proxy k -> Dict (KNodesConstraint k RZipMatch)
    recursiveZipMatch _ = Dict

instance RZipMatch Pure
instance Eq a => RZipMatch (Const a)

instance Recursive RZipMatch where
    {-# INLINE recurse #-}
    recurse = recursiveZipMatch . (const Proxy :: Proxy (RZipMatch k) -> Proxy k)

-- | 'ZipMatch' variant of 'Control.Applicative.liftA2'
{-# INLINE zipMatch2 #-}
zipMatch2 ::
    (ZipMatch k, KFunctor k) =>
    (forall n. KWitness k n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree k p -> Tree k q -> Maybe (Tree k r)
zipMatch2 f x y = zipMatch x y <&> mapK (\w (Pair a b) -> f w a b)

-- | Variant of 'zipMatch2' for functions with context instead of a witness parameter
{-# INLINE zipMatch2With #-}
zipMatch2With ::
    (ZipMatch k, KFunctor k, KNodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => Tree p n -> Tree q n -> Tree r n) ->
    Tree k p -> Tree k q -> Maybe (Tree k r)
zipMatch2With p f x y = zipMatch x y <&> mapKWith p (\(Pair a b) -> f a b)

-- | An 'Applicative' variant of 'zipMatch2'
{-# INLINE zipMatchA #-}
zipMatchA ::
    (Applicative f, ZipMatch k, KTraversable k) =>
    (forall n. KWitness k n -> Tree p n -> Tree q n -> f (Tree r n)) ->
    Tree k p -> Tree k q -> Maybe (f (Tree k r))
zipMatchA f x y = zipMatch x y <&> traverseK (\w (Pair a b) -> f w a b)

-- | An 'Applicative' variant of 'zipMatch2With'
{-# INLINE zipMatchWithA #-}
zipMatchWithA ::
    (Applicative f, ZipMatch k, KTraversable k, KNodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => Tree p n -> Tree q n -> f (Tree r n)) ->
    Tree k p -> Tree k q -> Maybe (f (Tree k r))
zipMatchWithA p f x y = zipMatch x y <&> traverseKWith p (\(Pair a b) -> f a b)

-- | A variant of 'zipMatchA' where the 'Applicative' actions do not contain results
{-# INLINE zipMatch_ #-}
zipMatch_ ::
    (Applicative f, ZipMatch k, KFoldable k) =>
    (forall n. KWitness k n -> Tree p n -> Tree q n -> f ()) ->
    Tree k p -> Tree k q -> Maybe (f ())
zipMatch_ f x y = zipMatch x y <&> traverseK_ (\w (Pair a b) -> f w a b)

-- | A variant of 'zipMatchWithA' where the 'Applicative' actions do not contain results
{-# INLINE zipMatchWith_ #-}
zipMatchWith_ ::
    (Applicative f, ZipMatch k, KFoldable k, KNodesConstraint k constraint) =>
    Proxy constraint ->
    (forall n. constraint n => Tree p n -> Tree q n -> f ()) ->
    Tree k p -> Tree k q -> Maybe (f ())
zipMatchWith_ p f x y = zipMatch x y <&> traverseKWith_ p (\(Pair a b) -> f a b)

-- | A variant of 'zipMatchWith_' for 'AST.Knot.Knot's with a single node type (avoids using @RankNTypes@)
{-# INLINE zipMatch1_ #-}
zipMatch1_ ::
    (Applicative f, ZipMatch k, KFoldable k, KNodesConstraint k ((~) n)) =>
    (Tree p n -> Tree q n -> f ()) ->
    Tree k p -> Tree k q -> Maybe (f ())
zipMatch1_ f x y = zipMatch x y <&> traverseK1_ (\(Pair a b) -> f a b)
