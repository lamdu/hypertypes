{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications #-}

module Hyper.Class.Context
    ( HContext(..)
    , recursiveContexts, recursiveContextsWith
    ) where

import Data.Constraint (withDict)
import Data.Functor.Const (Const(..))
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..))
import Hyper.Combinator.Ann (Ann(..))
import Hyper.Combinator.Func (HFunc(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (type (#))

import Prelude.Compat

class HContext h where
    hcontext ::
        h # p ->
        h # (HFunc p (Const (h # p)) :*: p)

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
