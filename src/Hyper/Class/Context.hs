{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications #-}

module Hyper.Class.Context
    ( HContext(..)
    , recursiveContexts
    ) where

import Hyper.Combinator.Ann (Ann(..))
import Hyper.Combinator.Func (HFunc(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (type (#))

import Hyper.Internal.Prelude

class HContext h where
    -- | Add next to each node a function to replace it in the parent with a different value
    hcontext ::
        h # p ->
        h # (HFunc p (Const (h # p)) :*: p)

-- | Add in the node annotations a function to replace each node in the top-level node
recursiveContexts ::
    (Recursively HContext h, Recursively HFunctor h) =>
    Ann p # h ->
    Ann (HFunc (Ann p) (Const (Ann p # h)) :*: p) # h
recursiveContexts = recursiveContextsWith . (HFunc Const :*:)

recursiveContextsWith ::
    forall h p r.
    (Recursively HContext h, Recursively HFunctor h) =>
    (HFunc (Ann p) (Const r) :*: Ann p) # h ->
    Ann (HFunc (Ann p) (Const r) :*: p) # h
recursiveContextsWith (HFunc s0 :*: Ann a b) =
    withDict (recursively (Proxy @(HContext h))) $
    withDict (recursively (Proxy @(HFunctor h)))
    Ann
    { _hAnn = HFunc s0 :*: a
    , _hVal =
        hmap
        ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
            \(HFunc s1 :*: x) ->
            recursiveContextsWith (HFunc (Const . getConst . s0 . Ann a . getConst . s1) :*: x)
        ) (hcontext b)
    }
