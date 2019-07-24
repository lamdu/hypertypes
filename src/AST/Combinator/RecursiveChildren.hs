{-# LANGUAGE NoImplicitPrelude, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module AST.Combinator.RecursiveChildren
    ( RecursiveChildren(..)
    ) where

import AST.Class.Combinators
import AST.Class.HasChildrenTypes
import AST.Class.Pointed
import AST.Class.Recursive
import AST.Combinator.Flip
import AST.Knot (Tree, Tie, RunKnot, ChildrenTypesOf)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy

import Prelude.Compat

data RecursiveChildren a k = RecursiveChildren
    { _recSelf :: Tie k a
    , _recSub :: Tree (ChildrenTypesOf a) (Flip RecursiveChildren (RunKnot k))
    }

type instance ChildrenTypesOf (RecursiveChildren a) = RecursiveChildren a

instance
    Recursive HasChildrenTypes a =>
    KPointed (RecursiveChildren a) where

    type KLiftConstraint (RecursiveChildren a) c = Recursive c a

    pureC = id

    pureK f =
        withDict (recursive :: RecursiveDict HasChildrenTypes a) $
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (Proxy :: Proxy '[Recursive HasChildrenTypes]) (_Flip # pureK f)
        }

    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive :: RecursiveDict HasChildrenTypes a) $
        withDict (hasChildrenTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (mkP p) (_Flip # pureKWithConstraint p f)
        }
        where
            recP :: Recursive c a => Proxy c -> RecursiveDict c a
            recP _ = recursive
            mkP :: Proxy c -> Proxy '[Recursive HasChildrenTypes, Recursive c]
            mkP _ = Proxy
