{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module Hyper.Class.Context
    ( HContext (..)
    , recursiveContexts
    , annContexts
    ) where

import Control.Lens (from, mapped, _1, _2, _Wrapped)
import Hyper.Class.Functor (HFunctor (..))
import Hyper.Class.Nodes ((#*#), (#>))
import Hyper.Class.Recursive (Recursively (..))
import Hyper.Combinator.Ann (Ann (..))
import Hyper.Combinator.Compose (HCompose (..), decompose, _HCompose)
import Hyper.Combinator.Flip
import Hyper.Combinator.Func (HFunc (..), _HFunc)
import Hyper.Type (type (#))
import Hyper.Type.Pure (Pure (..), _Pure)

import Hyper.Internal.Prelude

class HContext h where
    -- | Add next to each node a function to replace it in the parent with a different value
    hcontext ::
        h # p ->
        h # (HFunc p (Const (h # p)) :*: p)

instance HContext Pure where
    hcontext = _Pure %~ (HFunc (Const . Pure) :*:)

instance (HContext a, HFunctor a) => HContext (Ann a) where
    hcontext (Ann a b) =
        Ann
            (hmap (const (_1 . _HFunc . mapped . _Wrapped %~ (`Ann` b))) (hcontext a))
            (HFunc (Const . Ann a) :*: b)

instance (HFunctor c1, HContext c1, HFunctor h1, HContext h1) => HContext (HCompose c1 h1) where
    hcontext =
        _HCompose %~ layer (\c0 -> layer $ \c1 -> (HFunc ((_Wrapped %~ (_HCompose #)) . c0 . getConst . c1) :*:))
        where
            layer ::
                (HFunctor h, HContext h) =>
                (forall n. (p0 # HCompose q0 n -> Const (h # HCompose p0 q0) # n) -> p0 # HCompose q0 n -> p1 # HCompose q1 n) ->
                (h # HCompose p0 q0) ->
                h # HCompose p1 q1
            layer f = hmap (\_ (HFunc c :*: x) -> x & _HCompose %~ f (c . (_HCompose #))) . hcontext

instance (Recursively HContext h, Recursively HFunctor h) => HContext (HFlip Ann h) where
    -- The context of (HFlip Ann h) differs from annContexts in that
    -- only the annotation itself is replaced rather than the whole subexpression.
    hcontext =
        hmap (const (_1 . _HFunc . mapped . _Wrapped %~ (_HFlip #))) . (from hflipped %~ f . annContexts)
        where
            f ::
                forall n p r.
                Recursively HFunctor n =>
                Ann (HFunc (Ann p) (Const r) :*: p) # n ->
                Ann (HFunc p (Const r) :*: p) # n
            f (Ann (HFunc func :*: a) b) =
                Ann (HFunc (func . (`Ann` g b)) :*: a) (hmap (Proxy @(Recursively HFunctor) #> f) b)
                    \\ recursively (Proxy @(HFunctor n))
            g ::
                forall n a b.
                Recursively HFunctor n =>
                n # Ann (a :*: b) ->
                n # Ann b
            g =
                hmap (Proxy @(Recursively HFunctor) #> hflipped %~ hmap (const (^. _2)))
                    \\ recursively (Proxy @(HFunctor n))

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
    _HCompose
        # Ann
            { _hAnn = _HFunc # Const . getConst . s0 . (^. decompose)
            , _hVal =
                layer x0 $ \s1 x1 -> layer x1 $ \s2 x2 -> recursiveContextsWith (HFunc (Const . getConst . s0 . s1 . s2) :*: x2)
            }
    where
        layer ::
            forall t s c0 c1.
            (Recursively HFunctor t, Recursively HContext t) =>
            t # s ->
            (forall n. (Recursively HFunctor n, Recursively HContext n) => (s # n -> t # s) -> s # n -> HCompose c0 c1 # n) ->
            HCompose t c0 # c1
        layer x f =
            _HCompose # hmap (Proxy @(Recursively HContext) #*# Proxy @(Recursively HFunctor) #> \(HFunc s :*: v) -> f (getConst . s) v) (hcontext x)
                \\ recursively (Proxy @(HFunctor t))
                \\ recursively (Proxy @(HContext t))

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
    Ann
        { _hAnn = HFunc s0 :*: a
        , _hVal =
            hmap
                ( Proxy @(Recursively HContext) #*#
                    Proxy @(Recursively HFunctor) #>
                        \(HFunc s1 :*: x) ->
                            annContextsWith (HFunc (Const . getConst . s0 . Ann a . getConst . s1) :*: x)
                )
                (hcontext b)
                \\ recursively (Proxy @(HFunctor h))
                \\ recursively (Proxy @(HContext h))
        }
