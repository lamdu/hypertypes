{-# LANGUAGE NoImplicitPrelude, TypeFamilies, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables, DataKinds #-}

module AST.Combinator.RecursiveChildren
    ( RecursiveChildren(..)
    ) where

import AST.Class
import AST.Class.Combinators
import AST.Class.HasNodeTypes
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

type instance NodeTypesOf (RecursiveChildren a) = RecursiveChildren a

instance
    Recursive HasNodeTypes a =>
    HasNodeTypes (RecursiveChildren a)

instance
    Recursive HasNodeTypes a =>
    KPointed (RecursiveChildren a) where

    type KLiftConstraint (RecursiveChildren a) c = Recursive c a

    {-# INLINE pureC #-}
    pureC = id

    {-# INLINE pureK #-}
    pureK f =
        withDict (recursive :: RecursiveDict HasNodeTypes a) $
        withDict (hasNodeTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (Proxy :: Proxy '[Recursive HasNodeTypes]) (_Flip # pureK f)
        }

    {-# INLINE pureKWithConstraint #-}
    pureKWithConstraint p f =
        withDict (recP p) $
        withDict (recursive :: RecursiveDict HasNodeTypes a) $
        withDict (hasNodeTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = f
        , _recSub = pureKWith (mkP p) (_Flip # pureKWithConstraint p f)
        }
        where
            recP :: Recursive c a => Proxy c -> RecursiveDict c a
            recP _ = recursive
            mkP :: Proxy c -> Proxy '[Recursive HasNodeTypes, Recursive c]
            mkP _ = Proxy

instance
    Recursive HasNodeTypes a =>
    KFunctor (RecursiveChildren a) where

    {-# INLINE mapC #-}
    mapC (RecursiveChildren fSelf fSub) (RecursiveChildren xSelf xSub) =
        withDict (recursive :: RecursiveDict HasNodeTypes a) $
        withDict (hasNodeTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = runMapK fSelf xSelf
        , _recSub =
            mapC
            ( mapKWith (Proxy :: Proxy '[Recursive HasNodeTypes])
                ((_MapK #) . (\(MkFlip sf) -> _Flip %~ mapC sf)) fSub
            ) xSub
        }

instance
    Recursive HasNodeTypes a =>
    KApply (RecursiveChildren a) where

    {-# INLINE zipK #-}
    zipK (RecursiveChildren xSelf xSub) (RecursiveChildren ySelf ySub) =
        withDict (recursive :: RecursiveDict HasNodeTypes a) $
        withDict (hasNodeTypes (Proxy :: Proxy a)) $
        RecursiveChildren
        { _recSelf = Both xSelf ySelf
        , _recSub =
            liftK2With (Proxy :: Proxy '[Recursive HasNodeTypes])
            (\(MkFlip x) -> _Flip %~ zipK x) xSub ySub
        }
