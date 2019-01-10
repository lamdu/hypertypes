{-# LANGUAGE NoImplicitPrelude, DefaultSignatures, DataKinds, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module AST.Class.Instantiate
    ( Instantiate(..), SchemeType
    ) where

import AST.Class.Recursive
import AST.Class.Unify
import AST.Knot
import AST.Knot.Pure
import AST.Unify

type family SchemeType s :: Knot -> *

class Recursive (Unify m) (SchemeType s) => Instantiate m s where
    instantiate :: s -> m (Tree (UVar m) (SchemeType s))
    default instantiate ::
        (s ~ Tree Pure typ, SchemeType s ~ typ) =>
        s -> m (Tree (UVar m) (SchemeType s))
    instantiate = unfreeze
