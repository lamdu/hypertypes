-- | Classes applying on 'AHyperType's recursively

{-# LANGUAGE DefaultSignatures, FlexibleContexts, FlexibleInstances #-}

module Hyper.Class.Recursive
    ( Recursive(..)
    , Recursively(..)
    , RNodes, RTraversable
    ) where

import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure(..))
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A class of constraint constructors that apply to all recursive child nodes
class Recursive c where
    -- | Lift a recursive constraint to the next layer
    recurse :: (HNodes k, c k) => Proxy (c k) -> Dict (HNodesConstraint k c)

-- | A class of 'AHyperType's which recursively implement 'HNodes'
class HNodes k => RNodes k where
    recursiveHNodes :: Proxy k -> Dict (HNodesConstraint k RNodes)
    {-# INLINE recursiveHNodes #-}
    default recursiveHNodes ::
        HNodesConstraint k RNodes =>
        Proxy k -> Dict (HNodesConstraint k RNodes)
    recursiveHNodes _ = Dict

instance RNodes Pure
instance RNodes (Const a)

argP :: Proxy (f k :: Constraint) -> Proxy (k :: HyperType)
argP _ = Proxy

instance Recursive RNodes where
    {-# INLINE recurse #-}
    recurse = recursiveHNodes . argP

-- | A constraint lifted to apply recursively.
--
-- Note that in cases where a constraint has dependencies other than 'RNodes',
-- one will want to create a class such as RTraversable to capture the dependencies,
-- otherwise using it in class contexts will be quite unergonomic.
class RNodes k => Recursively c k where
    recursively ::
        Proxy (c k) -> Dict (c k, HNodesConstraint k (Recursively c))
    {-# INLINE recursively #-}
    default recursively ::
        (c k, HNodesConstraint k (Recursively c)) =>
        Proxy (c k) -> Dict (c k, HNodesConstraint k (Recursively c))
    recursively _ = Dict

instance Recursive (Recursively c) where
    {-# INLINE recurse #-}
    recurse p =
        withDict (recursively (p0 p)) Dict
        where
            p0 :: Proxy (Recursively c k) -> Proxy (c k)
            p0 _ = Proxy

instance c Pure => Recursively c Pure
instance c (Const a) => Recursively c (Const a)

-- | A class of 'AHyperType's which recursively implement 'HTraversable'
class (HTraversable k, Recursively HFunctor k, Recursively HFoldable k) => RTraversable k where
    recursiveHTraversable :: Proxy k -> Dict (HNodesConstraint k RTraversable)
    {-# INLINE recursiveHTraversable #-}
    default recursiveHTraversable ::
        HNodesConstraint k RTraversable =>
        Proxy k -> Dict (HNodesConstraint k RTraversable)
    recursiveHTraversable _ = Dict

instance RTraversable Pure
instance RTraversable (Const a)

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveHTraversable . argP
