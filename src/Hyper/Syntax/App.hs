{-# LANGUAGE FlexibleInstances, UndecidableInstances, TemplateHaskell, FlexibleContexts #-}

module Hyper.Syntax.App
    ( App(..), appFunc, appArg, W_App(..), MorphWitness(..)
    ) where

import Hyper
import Hyper.Class.Optic (HSubset(..), HSubset')
import Hyper.Infer
import Hyper.Syntax.FuncType
import Hyper.Unify (UnifyGen, unify)
import Hyper.Unify.New (newTerm, newUnbound)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Hyper.Internal.Prelude

-- | A term for function applications.
--
-- @App expr@s express function applications of @expr@s.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data App expr h = App
    { _appFunc :: h :# expr
    , _appArg :: h :# expr
    } deriving Generic

makeLenses ''App
makeZipMatch ''App
makeHContext ''App
makeHMorph ''App
makeHTraversableApplyAndBases ''App
makeCommonInstances [''App]

instance RNodes e => RNodes (App e)
instance (c (App e), Recursively c e) => Recursively c (App e)
instance RTraversable e => RTraversable (App e)

instance Pretty (h :# expr) => Pretty (App expr h) where
    pPrintPrec lvl p (App f x) =
        pPrintPrec lvl 10 f <+>
        pPrintPrec lvl 11 x
        & maybeParens (p > 10)

type instance InferOf (App e) = ANode (TypeOf e)

instance
    ( Infer m expr
    , HasInferredType expr
    , HSubset' (TypeOf expr) (FuncType (TypeOf expr))
    , UnifyGen m (TypeOf expr)
    ) =>
    Infer m (App expr) where

    {-# INLINE inferBody #-}
    inferBody (App func arg) =
        do
            InferredChild argI argR <- inferChild arg
            InferredChild funcI funcR <- inferChild func
            funcRes <- newUnbound
            (App funcI argI, MkANode funcRes) <$
                (newTerm (hSubset # FuncType (argR ^# l) funcRes) >>= unify (funcR ^# l))
        where
            l = inferredType (Proxy @expr)
