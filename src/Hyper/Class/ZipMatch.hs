-- | A class to match term structures

{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}

module Hyper.Class.ZipMatch
    ( ZipMatch(..)
    , zipMatch2
    , zipMatchA
    , zipMatch_, zipMatch1_
    ) where

import Control.Lens.Operators
import Control.Monad (guard)
import Data.Functor.Const (Const(..))
import GHC.Generics
import GHC.Generics.Lens (_M1, _Rec1)
import Hyper.Class.Foldable (HFoldable, htraverse_, htraverse1_)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..), HWitness)
import Hyper.Class.Traversable (HTraversable, htraverse)
import Hyper.Type (Tree)
import Hyper.Type.Pure (Pure(..), _Pure)

import Prelude.Compat

-- | A class to match term structures.
--
-- Similar to a partial version of 'Hyper.Class.Apply.Apply' but the semantics are different -
-- when the terms contain plain values, 'Hyper.Class.Apply.hzip' would append them,
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
    zipMatch :: Tree h p -> Tree h q -> Maybe (Tree h (p :*: q))
    default zipMatch ::
        (Generic1 h, ZipMatch (Rep1 h)) =>
        Tree h p -> Tree h q -> Maybe (Tree h (p :*: q))
    zipMatch x =
        fmap to1 . zipMatch (from1 x) . from1

instance ZipMatch Pure where
    {-# INLINE zipMatch #-}
    zipMatch (Pure x) (Pure y) = _Pure # (x :*: y) & Just

instance Eq a => ZipMatch (Const a) where
    {-# INLINE zipMatch #-}
    zipMatch (Const x) (Const y) = Const x <$ guard (x == y)

instance (ZipMatch a, ZipMatch b) => ZipMatch (a :*: b) where
    {-# INLINE zipMatch #-}
    zipMatch (a0 :*: b0) (a1 :*: b1) = (:*:) <$> zipMatch a0 a1 <*> zipMatch b0 b1

instance (ZipMatch a, ZipMatch b) => ZipMatch (a :+: b) where
    {-# INLINE zipMatch #-}
    zipMatch (L1 x) (L1 y) = zipMatch x y <&> L1
    zipMatch (R1 x) (R1 y) = zipMatch x y <&> R1
    zipMatch L1{} R1{} = Nothing
    zipMatch R1{} L1{} = Nothing

instance ZipMatch h => ZipMatch (M1 i m h) where
    {-# INLINE zipMatch #-}
    zipMatch = _M1 . zipMatch . (^. _M1)

instance ZipMatch h => ZipMatch (Rec1 h) where
    {-# INLINE zipMatch #-}
    zipMatch = _Rec1 . zipMatch . (^. _Rec1)

-- | 'ZipMatch' variant of 'Control.Applicative.liftA2'
{-# INLINE zipMatch2 #-}
zipMatch2 ::
    (ZipMatch h, HFunctor h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> Tree r n) ->
    Tree h p -> Tree h q -> Maybe (Tree h r)
zipMatch2 f x y = zipMatch x y <&> hmap (\w (a :*: b) -> f w a b)

-- | An 'Applicative' variant of 'zipMatch2'
{-# INLINE zipMatchA #-}
zipMatchA ::
    (Applicative f, ZipMatch h, HTraversable h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> f (Tree r n)) ->
    Tree h p -> Tree h q -> Maybe (f (Tree h r))
zipMatchA f x y = zipMatch x y <&> htraverse (\w (a :*: b) -> f w a b)

-- | A variant of 'zipMatchA' where the 'Applicative' actions do not contain results
{-# INLINE zipMatch_ #-}
zipMatch_ ::
    (Applicative f, ZipMatch h, HFoldable h) =>
    (forall n. HWitness h n -> Tree p n -> Tree q n -> f ()) ->
    Tree h p -> Tree h q -> Maybe (f ())
zipMatch_ f x y = zipMatch x y <&> htraverse_ (\w (a :*: b) -> f w a b)

-- | A variant of 'zipMatch_' for 'Hyper.Type.HyperType's with a single node type (avoids using @RankNTypes@)
{-# INLINE zipMatch1_ #-}
zipMatch1_ ::
    (Applicative f, ZipMatch h, HFoldable h, HNodesConstraint h ((~) n)) =>
    (Tree p n -> Tree q n -> f ()) ->
    Tree h p -> Tree h q -> Maybe (f ())
zipMatch1_ f x y = zipMatch x y <&> htraverse1_ (\(a :*: b) -> f a b)
