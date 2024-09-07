{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances, PolyKinds #-}

-- An attempt to translate compdata's Data.Comp.Multi.Ops subsumption mechanism to hypertypes

module Hyper.Class.Subsume (
    Subsume(..), (:<:)
) where

import Data.Proxy
import GHC.Generics

import Prelude.Compat

data Pos = Here | Le Pos | Ri Pos | Sum Pos Pos

data Emb = Found Pos | NotFound | Ambiguous

type family Sum' e1 r where
    Sum' (Found x) (Found y) = Found (Sum x y)
    Sum' Ambiguous y = Ambiguous
    Sum' x Ambiguous = Ambiguous
    Sum' NotFound y = NotFound
    Sum' x NotFound = NotFound

type family Choose e1 r where
    Choose (Found x) (Found y) = Ambiguous
    Choose Ambiguous y = Ambiguous
    Choose x Ambiguous = Ambiguous
    Choose (Found x) y = Found (Le x)
    Choose x (Found y) = Found (Ri y)
    Choose x y = NotFound

type family Elem f g where
    Elem f f = Found Here
    Elem (f1 :+: f2) g = Sum' (Elem f1 g) (Elem f2 g)
    Elem f (g1 :+: g2) = Choose (Elem f g1) (Elem f g2)
    Elem f g = NotFound

class Subsume (e :: Emb) f g where
    inj' :: Proxy e -> f a -> g a
    prj' :: Proxy e -> g a -> Maybe (f a)

instance Subsume (Found Here) f f where
    inj' _ = id
    prj' _ = Just

instance Subsume (Found p) f g => Subsume (Found (Le p)) f (g :+: g') where
    inj' _ = L1 . inj' (Proxy @(Found p))

    prj' _ (L1 x) = prj' (Proxy @(Found p)) x
    prj' _ _ = Nothing

instance Subsume (Found p) f g => Subsume (Found (Ri p)) f (g' :+: g) where
    inj' _ = R1 . inj' (Proxy @(Found p))

    prj' _ (R1 x) = prj' (Proxy @(Found p)) x
    prj' _ _ = Nothing

instance (Subsume (Found p1) f1 g, Subsume (Found p2) f2 g)
    => Subsume (Found (Sum p1 p2)) (f1 :+: f2) g where
    inj' _ (L1 x) = inj' (Proxy @(Found p1)) x
    inj' _ (R1 x) = inj' (Proxy @(Found p2)) x

    prj' _ x =
        case prj' (Proxy @(Found p1)) x of
        Just y -> Just (L1 y)
        _ ->
            case prj' (Proxy @(Found p2)) x of
            Just y -> Just (R1 y)
            _ -> Nothing

type family OrDupl' a (b :: [Pos]) where
    OrDupl' True _ = True
    OrDupl' False c = Dupl' c

type family Find (p :: Pos) (s :: [Pos]) where
    Find p '[] = False
    Find p (p ': r)  = True
    Find p (p' ': r) = Find p r

type family Dupl' (s :: [Pos]) where
    Dupl' '[] = False
    Dupl' (p ': r) = OrDupl' (Find p r) r

type family ToList s where
    ToList '[] = '[]
    ToList (Sum p1 p2 ': s) = ToList (p1 ': p2 ': s)
    ToList (p ': s) = p ': ToList s

type Dupl s = Dupl' (ToList '[s])

type family Check b p where
    Check False p = Found p
    Check True  p = Ambiguous

type family CombineMaybe p p' where
    CombineMaybe p (Just p') = p'
    CombineMaybe p _ = p

type family Le' p where
    Le' Nothing = Nothing
    Le' (Just p) = Just (Le p)

type family Ri' p where
    Ri' Nothing = Nothing
    Ri' (Just p) = Just (Ri p)

type family Combine l r where
    Combine (Le l) (Le r) = Le' (Combine l r)
    Combine (Ri l) (Ri r) = Ri' (Combine l r)
    Combine (Le Here) (Ri Here) = Just Here
    Combine l r = Nothing

type family CombineRec l r where
    CombineRec l r = CombineMaybe (Sum l r) (Combine l r)

type family ComprPos p where
    ComprPos Here = Here
    ComprPos (Le p) = Le (ComprPos p)
    ComprPos (Ri p) = Ri (ComprPos p)
    ComprPos (Sum l r) = CombineRec (ComprPos l) (ComprPos r)

type family ComprEmb e where
    ComprEmb (Found p) = Check (Dupl p) (ComprPos p)
    ComprEmb e = e

-- | A constraint @f :<: g@ expresses that the signature @f@ is
-- subsumed by @g@, i.e. @f@ can be used to construct elements in @g@.
type f :<: g = Subsume (ComprEmb (Elem f g)) f g
