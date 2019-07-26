{-# LANGUAGE NoImplicitPrelude, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module AST.Combinator.RecursiveChildren
    ( RecursiveChildren(..)
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.Recursive
import AST.Combinator.Both
import AST.Combinator.Flip
import AST.Knot (Tree, Node, RunKnot)
import Control.Lens.Operators
import Data.Constraint
import Data.Proxy

import Prelude.Compat

data RecursiveChildren a k = RecursiveChildren
    { _recSelf :: Node k a
    , _recSub :: Tree (NodeTypesOf a) (Flip RecursiveChildren (RunKnot k))
    }

instance
    Recursively HasNodes a =>
    HasNodes (RecursiveChildren a) where
    type NodeTypesOf (RecursiveChildren a) = RecursiveChildren a
    type NodesConstraint (RecursiveChildren a) = RecursiveConstraint a

instance
    Recursively HasNodes a =>
    KPointed (RecursiveChildren a) where

    {-# INLINE pureK #-}
    pureK f =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (Proxy :: Proxy '[Recursively HasNodes]) (_Flip # pureK f)
        }

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (mkP p) (_Flip # pureKWithConstraint p f)
        }
        where
            recP :: Recursively c a => Proxy c -> RecursiveDict a c
            recP _ = recursive
            mkP :: Proxy c -> Proxy '[Recursively HasNodes, Recursively c]
            mkP _ = Proxy

instance
    Recursively HasNodes a =>
    KFunctor (RecursiveChildren a) where

    {-# INLINE mapC #-}
    mapC (RecursiveChildren fSelf fSub) (RecursiveChildren xSelf xSub) =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = runMapK fSelf xSelf
        , _recSub =
            mapC
            ( mapKWith (Proxy :: Proxy '[Recursively HasNodes])
                ((_MapK #) . (\(MkFlip sf) -> _Flip %~ mapC sf)) fSub
            ) xSub
        }

instance
    Recursively HasNodes a =>
    KApply (RecursiveChildren a) where

    {-# INLINE zipK #-}
    zipK (RecursiveChildren xSelf xSub) (RecursiveChildren ySelf ySub) =
        withDict (recursive :: RecursiveDict a HasNodes) $
        withDict (hasNodes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = Both xSelf ySelf
        , _recSub =
            liftK2With (Proxy :: Proxy '[Recursively HasNodes])
            (\(MkFlip x) -> _Flip %~ zipK x) xSub ySub
        }
