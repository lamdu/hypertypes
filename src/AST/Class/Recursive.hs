{-# LANGUAGE DefaultSignatures, FlexibleContexts, FlexibleInstances #-}

module AST.Class.Recursive
    ( Recursive(..)
    , Recursively(..)
    , RNodes, RTraversable
    ) where

import AST.Class.Foldable
import AST.Class.Functor (KFunctor(..))
import AST.Class.Nodes (KNodes(..))
import AST.Class.Traversable
import AST.Knot
import AST.Knot.Pure (Pure(..))
import Data.Constraint (Dict(..), withDict)
import Data.Functor.Const (Const(..))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy(..))

import Prelude.Compat

-- | A class of constraint constructors that apply to all recursive child nodes
class Recursive c where
    -- | Lift a recursive constraint to the next layer
    recurse :: (KNodes k, c k) => Proxy (c k) -> Dict (KNodesConstraint k c)

-- | A class of 'Knot's which recursively implement 'KNodes'
class KNodes k => RNodes k where
    recursiveKNodes :: Proxy k -> Dict (KNodesConstraint k RNodes)
    {-# INLINE recursiveKNodes #-}
    default recursiveKNodes ::
        KNodesConstraint k RNodes =>
        Proxy k -> Dict (KNodesConstraint k RNodes)
    recursiveKNodes _ = Dict

instance RNodes Pure
instance RNodes (Const a)

argP :: Proxy (f k :: Constraint) -> Proxy (k :: Knot -> Type)
argP _ = Proxy

instance Recursive RNodes where
    {-# INLINE recurse #-}
    recurse = recursiveKNodes . argP

-- | A constraint lifted to apply recursively.
--
-- Note that in cases where a constraint has dependencies other than 'RNodes',
-- one will want to create a class such as RTraversable to capture the dependencies,
-- otherwise using it in class contexts will be quite unergonomic.
class RNodes k => Recursively c k where
    recursively ::
        Proxy (c k) -> Dict (c k, KNodesConstraint k (Recursively c))
    {-# INLINE recursively #-}
    default recursively ::
        (c k, KNodesConstraint k (Recursively c)) =>
        Proxy (c k) -> Dict (c k, KNodesConstraint k (Recursively c))
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

-- | A class of 'Knot's which recursively implement 'KTraversable'
class (KTraversable k, Recursively KFunctor k, Recursively KFoldable k) => RTraversable k where
    recursiveKTraversable :: Proxy k -> Dict (KNodesConstraint k RTraversable)
    {-# INLINE recursiveKTraversable #-}
    default recursiveKTraversable ::
        KNodesConstraint k RTraversable =>
        Proxy k -> Dict (KNodesConstraint k RTraversable)
    recursiveKTraversable _ = Dict

instance RTraversable Pure
instance RTraversable (Const a)

instance Recursive RTraversable where
    {-# INLINE recurse #-}
    recurse = recursiveKTraversable . argP
