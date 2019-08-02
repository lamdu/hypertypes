{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module AST.Knot.Dict
    ( KDict(..), _KDict
    , pureKWithDict, mapKWithDict
    ) where

import AST.Class
import AST.Knot (Tree, RunKnot)
import Control.Lens (Iso, iso)
import Data.Constraint (Dict(..), withDict)
import Data.Constraint.List (ApplyConstraints)
import Data.Proxy (Proxy(..))

newtype KDict cs k = MkKDict { getKDict :: Dict (ApplyConstraints cs (RunKnot k)) }

{-# INLINE _KDict #-}
_KDict ::
    Iso (Tree (KDict cs0) k0)
        (Tree (KDict cs1) k1)
        (Dict (ApplyConstraints cs0 k0))
        (Dict (ApplyConstraints cs1 k1))
_KDict = iso getKDict MkKDict

{-# INLINE pureKWithDict #-}
pureKWithDict ::
    KFunctor k =>
    Tree k (KDict constraints) ->
    (forall child. ApplyConstraints constraints child => Tree n child) ->
    Tree k n
pureKWithDict c f = mapK (\(MkKDict d) -> withDict d f) c

{-# INLINE mapKWithDict #-}
mapKWithDict ::
    forall k m n constraints.
    KFunctor k =>
    Tree (NodeTypesOf k) (KDict constraints) ->
    (forall child. ApplyConstraints constraints child => Tree m child -> Tree n child) ->
    Tree k m ->
    Tree k n
mapKWithDict c f =
    withDict (kNodes (Proxy @k))
    (mapC (pureKWithDict c (MkMapK f)))
