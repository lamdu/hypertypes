-- | A class to match term structures

module Hyper.Class.ZipMatch
    ( ZipMatch(..)
    , zipMatch2
    , zipMatchA
    , zipMatch_, zipMatch1_
    ) where

import Control.Lens.Operators
import Control.Monad (guard)
import Data.Functor.Const (Const(..))
import Data.Functor.Product.PolyKinds (Product(..))
import Data.Functor.Sum.PolyKinds (Sum(..))
import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Traversable (HTraversable, traverseH)
import Hyper.Type (Tree)
import Hyper.Type.Pure (Pure(..), _Pure)

import Prelude.Compat

-- | A class to match term structures.
--
-- Similar to a partial version of 'Hyper.Class.Apply.Apply' but the semantics are different -
-- when the terms contain plain values, 'Hyper.Class.Apply.zipH' would append them,
-- but 'zipMatch' would compare them and only produce a result if they match.
--
-- The @TemplateHaskell@ generators 'Hyper.TH.Apply.makeHApply' and 'Hyper.TH.ZipMatch.makeZipMatch'
-- create the instances according to these semantics.
class ZipMatch h where
    -- | Compare two structures
    --
    -- >>> zipMatch (NewPerson p0) (NewPerson p1)
    -- Just (NewPerson (Pair p0 p1))
    -- >>> zipMatch (NewPerson p) (NewCake c)
    -- Nothing
    zipMatch :: Tree h p -> Tree h q -> Maybe (Tree h (Product p q))

instance Eq a => ZipMatch (Const a) where
    {-# INLINE zipMatch #-}
    zipMatch (Const x) (Const y) = Const x <$ guard (x == y)

instance (ZipMatch a, ZipMatch b) => ZipMatch (Product a b) where
    {-# INLINE zipMatch #-}
    zipMatch (Pair a0 b0) (Pair a1 b1) = Pair <$> zipMatch a0 a1 <*> zipMatch b0 b1

instance (ZipMatch a, ZipMatch b) => ZipMatch (Sum a b) where
    {-# INLINE zipMatch #-}
    zipMatch (InL x) (InL y) = zipMatch x y <&> InL
    zipMatch (InR x) (InR y) = zipMatch x y <&> InR
    zipMatch InL{} InR{} = Nothing
    zipMatch InR{} InL{} = Nothing

instance ZipMatch Pure where
    {-# INLINE zipMatch #-}
    zipMatch (Pure x) (Pure y) = _Pure # Pair x y & Just

-- | 'ZipMatch' variant of 'Control.Applicative.liftA2'
{-# INLINE zipMatch2 #-}
zipMatch2 ::
    (ZipMatch h, HFunctor h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree h p -> Tree h q -> Maybe (Tree h r)
zipMatch2 f x y = zipMatch x y <&> mapH (\w (Pair a b) -> f w a b)

-- | An 'Applicative' variant of 'zipMatch2'
{-# INLINE zipMatchA #-}
zipMatchA ::
    (Applicative f, ZipMatch h, HTraversable h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> f (Tree r n)) ->
    Tree h p -> Tree h q -> Maybe (f (Tree h r))
zipMatchA f x y = zipMatch x y <&> traverseH (\w (Pair a b) -> f w a b)

-- | A variant of 'zipMatchA' where the 'Applicative' actions do not contain results
{-# INLINE zipMatch_ #-}
zipMatch_ ::
    (Applicative f, ZipMatch h, HFoldable h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> f ()) ->
    Tree h p -> Tree h q -> Maybe (f ())
zipMatch_ f x y = zipMatch x y <&> traverseH_ (\w (Pair a b) -> f w a b)

-- | A variant of 'zipMatch_' for 'Hyper.Type.HyperType's with a single node type (avoids using @RankNTypes@)
{-# INLINE zipMatch1_ #-}
zipMatch1_ ::
    (Applicative f, ZipMatch h, HFoldable h, HNodesConstraint h ((~) n)) =>
    (Tree p n -> Tree q n -> f ()) ->
    Tree h p -> Tree h q -> Maybe (f ())
zipMatch1_ f x y = zipMatch x y <&> traverseH1_ (\(Pair a b) -> f a b)
