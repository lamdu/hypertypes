{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeApplications #-}

module Hyper.Class.Context
    ( HContext(..)
    , recursiveContexts, recursiveContextsWith
    ) where

import Data.Constraint (withDict)
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..))
import Hyper.Combinator.Ann (Ann(..))
import Hyper.Combinator.Cont (HCont(..))
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Type (Tree)

import Prelude.Compat

class HContext h where
    hcontext ::
        Tree h p ->
        Tree h (HCont (Tree h p) p :*: p)

recursiveContexts ::
    (Recursively HContext h, Recursively HFunctor h) =>
    Tree (Ann p) h ->
    Tree (Ann (HCont (Tree (Ann p) h) p :*: p)) h
recursiveContexts = recursiveContextsWith . (HCont id :*:)

recursiveContextsWith ::
    forall h p r.
    (Recursively HContext h, Recursively HFunctor h) =>
    Tree (HCont r (Ann p) :*: Ann p) h ->
    Tree (Ann (HCont r p :*: p)) h
recursiveContextsWith (HCont s0 :*: Ann a b) =
    withDict (recursively (Proxy @(HContext h))) $
    withDict (recursively (Proxy @(HFunctor h)))
    Ann
    { _hAnn = HCont (s0 . (`Ann` b)) :*: a
    , _hVal =
        hmap
        ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
            \(HCont s1 :*: x) ->
            recursiveContextsWith (HCont (s0 . Ann a . s1) :*: x)
        ) (hcontext b)
    }
