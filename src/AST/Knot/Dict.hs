{-# LANGUAGE NoImplicitPrelude, RankNTypes, TypeFamilies, TypeOperators, DataKinds #-}

module AST.Knot.Dict
    ( KDict(..), _KDict
    , ApplyKConstraints
    , pureKWithDict
    ) where

import AST.Class
import AST.Knot (Tree, Knot, RunKnot)
import Control.Lens (Iso, iso)
import Data.Constraint (Dict(..), Constraint, withDict)
import Data.Kind (Type)

type family ApplyKConstraints (k :: Knot -> Type) cs :: Constraint where
    ApplyKConstraints k (c ': cs) = (c k, ApplyKConstraints k cs)
    ApplyKConstraints k '[] = ()

newtype KDict cs k = MkKDict { getKDict :: Dict (ApplyKConstraints (RunKnot k) cs) }

{-# INLINE _KDict #-}
_KDict ::
    Iso (Tree (KDict cs0) k0)
        (Tree (KDict cs1) k1)
        (Dict (ApplyKConstraints k0 cs0))
        (Dict (ApplyKConstraints k1 cs1))
_KDict = iso getKDict MkKDict

{-# INLINE pureKWithDict #-}
pureKWithDict ::
    KFunctor k =>
    Tree k (KDict constraints) ->
    (forall child. ApplyKConstraints child constraints => Tree n child) ->
    Tree k n
pureKWithDict c f = mapK (\(MkKDict d) -> withDict d f) c
