-- | Classes applying on 'HyperType's recursively

{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Hyper.Class.Recursive
    ( Recursive(..)
    , Recursively(..)
    , RNodes, RTraversable
    ) where

import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint)
import Data.Proxy (Proxy(..))
import Hyper.Class.Foldable
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes (HNodes(..))
import Hyper.Class.Traversable
import Hyper.Type
import Hyper.Type.Pure (Pure(..))

import Prelude.Compat

-- | A class of constraint constructors that apply to all recursive child nodes
class Recursive c where
    -- | Lift a recursive constraint to the next layer
    recurse :: (HNodes h, c h) => Proxy (c h) -> Dict (HNodesConstraint h c)

-- | A class of 'HyperType's which recursively implement 'HNodes'
class HNodes h => RNodes h where
    recursiveHNodes :: Proxy h -> Dict (HNodesConstraint h RNodes)
    {-# INLINE recursiveHNodes #-}
    default recursiveHNodes ::
        HNodesConstraint h RNodes =>
        Proxy h -> Dict (HNodesConstraint h RNodes)
    recursiveHNodes _ = Dict

instance RNodes Pure
instance RNodes (Const a)

argP :: Proxy (f h :: Constraint) -> Proxy (h :: HyperType)
argP _ = Proxy

instance Recursive RNodes where
    {-# INLINE recurse #-}
    recurse = recursiveHNodes . argP

-- | A constraint lifted to apply recursively.
--
-- Note that in cases where a constraint has dependencies other than 'RNodes',
-- one will want to create a class such as RTraversable to capture the dependencies,
-- otherwise using it in class contexts will be quite unergonomic.
class RNodes h => Recursively c h where
    recursively ::
        Proxy (c h) -> Dict (c h, HNodesConstraint h (Recursively c))
    {-# INLINE recursively #-}
    default recursively ::
        (c h, HNodesConstraint h (Recursively c)) =>
        Proxy (c h) -> Dict (c h, HNodesConstraint h (Recursively c))
    recursively _ = Dict

instance Recursive (Recursively c) where
    {-# INLINE recurse #-}
    recurse p =
        withDict (recursively (p0 p)) Dict
        where
            p0 :: Proxy (Recursively c h) -> Proxy (c h)
            p0 _ = Proxy

instance c Pure => Recursively c Pure
instance c (Const a) => Recursively c (Const a)

-- | A class of 'HyperType's which recursively implement 'HTraversable'
class (HTraversable h, Recursively HFunctor h, Recursively HFoldable h) => RTraversable h where
    recursiveHTraversable :: Proxy h -> Dict (HNodesConstraint h RTraversable)
    {-# INLINE recursiveHTraversable #-}
    default recursiveHTraversable ::
        HNodesConstraint h RTraversable =>
        Proxy h -> Dict (HNodesConstraint h RTraversable)
    recursiveHTraversable _ = Dict

instance RTraversable Pure
instance RTraversable (Const a)

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveHTraversable . argP
