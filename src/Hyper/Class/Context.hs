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
import Hyper.Combinator.Cont (HCont(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (type (#))

import Prelude.Compat

class HContext h where
    hcontext ::
        h # p ->
        h # (HCont (Const (h # p)) p :*: p)

recursiveContexts ::
    (Recursively HContext h, Recursively HFunctor h) =>
    Ann p # h ->
    Ann (HCont (Const (Ann p # h)) (Ann p) :*: p) # h
recursiveContexts = recursiveContextsWith . (HCont Const :*:)

recursiveContextsWith ::
    forall h p r.
    (Recursively HContext h, Recursively HFunctor h) =>
    (HCont (Const r) (Ann p) :*: Ann p) # h ->
    Ann (HCont (Const r) (Ann p) :*: p) # h
recursiveContextsWith (HCont s0 :*: Ann a b) =
    withDict (recursively (Proxy @(HContext h))) $
    withDict (recursively (Proxy @(HFunctor h)))
    Ann
    { _hAnn = HCont s0 :*: a
    , _hVal =
        hmap
        ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
            \(HCont s1 :*: x) ->
            recursiveContextsWith (HCont (Const . getConst . s0 . Ann a . getConst . s1) :*: x)
        ) (hcontext b)
    }
