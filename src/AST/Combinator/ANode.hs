{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}

module AST.Combinator.ANode
    ( ANode(..), _ANode
    , traverseK1, traverseK1_
    ) where

import AST.Class
import AST.Class.Foldable
import AST.Class.Traversable
import AST.Knot (Tree, Node)
import AST.TH.Pointed (makeKPointed)
import Control.DeepSeq (NFData)
import Control.Lens (Iso, iso)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Foldable (sequenceA_)
import Data.Functor.Product.PolyKinds
import Data.TyFun (On)
import GHC.Generics (Generic)

import Prelude.Compat

newtype ANode c k = MkANode { getANode :: Node k c }
    deriving stock Generic

{-# INLINE _ANode #-}
_ANode :: Iso (Tree (ANode c0) k0) (Tree (ANode c1) k1) (Tree k0 c0) (Tree k1 c1)
_ANode = iso getANode MkANode

instance KNodes (ANode c) where
    type NodeTypesOf (ANode c) = ANode c
    type NodesConstraint (ANode c) = On c

makeKPointed ''ANode

instance KApply (ANode c) where
    {-# INLINE zipK #-}
    zipK = (_ANode %~) . (Pair . getANode)

instance KFoldable (ANode c) where
    foldMapC f = (f ^. _ANode . _ConvertK) . getANode
    {-# INLINE foldMapK #-}
    foldMapK = (. getANode)
    {-# INLINE foldMapKWith #-}
    foldMapKWith _ = (. getANode)

instance KFunctor (ANode c) where
    mapC = (_ANode %~) . (^. _ANode . _MapK)
    {-# INLINE mapK #-}
    mapK = (_ANode %~)
    {-# INLINE mapKWithConstraint #-}
    mapKWithConstraint _ = (_ANode %~)

instance KTraversable (ANode c) where sequenceC = _ANode runContainedK

{-# INLINE foldMapK1 #-}
foldMapK1 ::
    ( Monoid a, KFoldable k
    , NodeTypesOf k ~ ANode c
    ) =>
    (Tree l c -> a) ->
    Tree k l ->
    a
foldMapK1 = foldMapC . MkANode . MkConvertK

{-# INLINE traverseK1_ #-}
traverseK1_ ::
    ( Applicative f, KFoldable k
    , NodeTypesOf k ~ ANode c
    ) =>
    (Tree m c -> f ()) ->
    Tree k m ->
    f ()
traverseK1_ f = sequenceA_ . foldMapK1 ((:[]) . f)

{-# INLINE traverseK1 #-}
traverseK1 ::
    ( Applicative f, KTraversable k
    , NodeTypesOf k ~ ANode c
    ) =>
    (Tree m c -> f (Tree n c)) ->
    Tree k m ->
    f (Tree k n)
traverseK1 f = sequenceC . mapC (MkANode (MkMapK (MkContainedK . f)))

deriving instance Eq   (Node k c) => Eq   (ANode c k)
deriving instance Ord  (Node k c) => Ord  (ANode c k)
deriving instance Show (Node k c) => Show (ANode c k)
instance Binary (Node k c) => Binary (ANode c k)
instance NFData (Node k c) => NFData (ANode c k)
