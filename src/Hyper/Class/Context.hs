{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Hyper.Class.Context
    ( HContext(..)
    , recursiveContexts, annContexts
    ) where

import Control.Lens (mapped, from, _Wrapped, _1, _2)
import Hyper.Combinator.Compose (HCompose(..), _HCompose, decompose)
import Hyper.Combinator.Flip
import Hyper.Combinator.Func (HFunc(..), _HFunc)
import Hyper.Class.Functor (HFunctor(..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively(..))
import Hyper.Combinator.Ann (Ann(..))
import Hyper.Type (type (#))
import Hyper.Type.Pure (Pure(..), _Pure)

import Hyper.Internal.Prelude

class HContext h where
    -- | Add next to each node a function to replace it in the parent with a different value
    hcontext ::
        h # p ->
        h # (HFunc p (Const (h # p)) :*: p)

instance HContext Pure where
    hcontext = _Pure %~ \x -> HFunc (Const . Pure) :*: x

instance (HContext a, HFunctor a) => HContext (Ann a) where
    hcontext (Ann a b) =
        Ann
        (hmap (const (_1 . _HFunc . mapped . _Wrapped %~ (`Ann` b))) (hcontext a))
        (HFunc (Const . Ann a) :*: b)

instance (HFunctor h0, HContext h0, HFunctor h1, HContext h1) => HContext (HCompose h0 h1) where
    hcontext =
        _HCompose %~
        hmap
        ( \_ (HFunc c0 :*: x0) ->
            x0 & _HCompose %~
            hmap
            ( \_ (HFunc c1 :*: x1) ->
                x1 & _HCompose %~
                (HFunc (Const . (_HCompose #) . getConst . c0 . (_HCompose #) . getConst . c1 . (_HCompose #)) :*:)
            ) . hcontext
        ) . hcontext

instance (Recursively HContext h, Recursively HFunctor h) => HContext (HFlip Ann h) where
    -- The context of (HFlip Ann h) differs from annContexts in that
    -- only the annotation itself is replaced rather than the whole subexpression.
    hcontext =
        hmap (const (_1 . _HFunc . mapped . _Wrapped %~ (_HFlip #))) . (from hflipped %~ f . annContexts)
        where
            f ::
                forall n p r.
                Recursively HFunctor n =>
                Ann (HFunc (Ann p) (Const r) :*: p) # n -> Ann (HFunc p (Const r) :*: p) # n
            f (Ann (HFunc func :*: a) b) =
                withDict (recursively (Proxy @(HFunctor n))) $
                Ann (HFunc (func . (`Ann` g b)) :*: a) (hmap (Proxy @(Recursively HFunctor) #> f) b)
            g ::
                forall n a b.
                Recursively HFunctor n => n # Ann (a :*: b) -> n # Ann b
            g =
                withDict (recursively (Proxy @(HFunctor n))) $
                hmap (Proxy @(Recursively HFunctor) #> hflipped %~ hmap (const (^. _2)))

-- | Add in the node annotations a function to replace each node in the top-level node
recursiveContexts ::
    (Recursively HContext h, Recursively HFunctor h, Recursively HContext p, Recursively HFunctor p) =>
    p # h ->
    HCompose (Ann (HFunc Pure (Const (p # h)))) p # h
recursiveContexts = recursiveContextsWith . (HFunc Const :*:)

recursiveContextsWith ::
    forall h p r.
    (Recursively HContext h, Recursively HFunctor h, Recursively HContext p, Recursively HFunctor p) =>
    (HFunc p (Const r) :*: p) # h ->
    HCompose (Ann (HFunc Pure (Const r))) p # h
recursiveContextsWith (HFunc s0 :*: x0) =
    withDict (recursively (Proxy @(HFunctor p))) $
    withDict (recursively (Proxy @(HFunctor h))) $
    withDict (recursively (Proxy @(HContext p))) $
    withDict (recursively (Proxy @(HContext h))) $
    _HCompose # Ann
    { _hAnn = _HFunc # Const . getConst . s0 . (^. decompose)
    , _hVal =
        _HCompose #
        hmap
        ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
            \(HFunc s1 :*: x1) ->
            _HCompose #
            hmap
            ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
                \(HFunc s2 :*: x2) ->
                recursiveContextsWith (HFunc (Const . getConst . s0 . getConst . s1 . getConst . s2) :*: x2)
            ) (hcontext x1)
        ) (hcontext x0)
    }

-- | Add in the node annotations a function to replace each node in the top-level node
--
-- It is possible to define annContexts in terms of 'recursiveContexts' but the conversion is quite unwieldy.
annContexts ::
    (Recursively HContext h, Recursively HFunctor h) =>
    Ann p # h ->
    Ann (HFunc (Ann p) (Const (Ann p # h)) :*: p) # h
annContexts = annContextsWith . (HFunc Const :*:)

annContextsWith ::
    forall h p r.
    (Recursively HContext h, Recursively HFunctor h) =>
    (HFunc (Ann p) (Const r) :*: Ann p) # h ->
    Ann (HFunc (Ann p) (Const r) :*: p) # h
annContextsWith (HFunc s0 :*: Ann a b) =
    withDict (recursively (Proxy @(HContext h))) $
    withDict (recursively (Proxy @(HFunctor h)))
    Ann
    { _hAnn = HFunc s0 :*: a
    , _hVal =
        hmap
        ( Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #>
            \(HFunc s1 :*: x) ->
            annContextsWith (HFunc (Const . getConst . s0 . Ann a . getConst . s1) :*: x)
        ) (hcontext b)
    }
