{-# LANGUAGE FlexibleInstances, UndecidableInstances, TemplateHaskell #-}

module Hyper.Type.AST.App
    ( App(..), appFunc, appArg, W_App(..)
    , appChildren
    ) where

import Control.Lens (Traversal, makeLenses)
import Control.Lens.Operators
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Hyper
import Hyper.Infer
import Hyper.TH.Internal.Instances (makeCommonInstances)
import Hyper.Type.AST.FuncType
import Hyper.Unify (Unify, unify)
import Hyper.Unify.New (newTerm, newUnbound)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Prelude.Compat

-- | A term for function applications.
--
-- @App expr@s express function applications of @expr@s.
--
-- Apart from the data type, an 'Infer' instance is also provided.
data App expr h = App
    { _appFunc :: h # expr
    , _appArg :: h # expr
    } deriving Generic

makeLenses ''App
makeZipMatch ''App
makeHContext ''App
makeHTraversableApplyAndBases ''App
makeCommonInstances [''App]

instance RNodes e => RNodes (App e)
instance (c (App e), Recursively c e) => Recursively c (App e)
instance RTraversable e => RTraversable (App e)

instance Pretty (h # expr) => Pretty (App expr h) where
    pPrintPrec lvl p (App f x) =
        pPrintPrec lvl 10 f <+>
        pPrintPrec lvl 11 x
        & maybeParens (p > 10)

-- | Type changing traversal from 'App' to its child nodes
appChildren ::
    Traversal (App t0 f0) (App t1 f1) (f0 # t0) (f1 # t1)
appChildren f (App x0 x1) = App <$> f x0 <*> f x1

type instance InferOf (App e) = ANode (TypeOf e)

instance
    ( Infer m expr
    , HasInferredType expr
    , HasFuncType (TypeOf expr)
    , Unify m (TypeOf expr)
    ) =>
    Infer m (App expr) where

    {-# INLINE inferBody #-}
    inferBody (App func arg) =
        do
            InferredChild argI argR <- inferChild arg
            InferredChild funcI funcR <- inferChild func
            funcRes <- newUnbound
            (App funcI argI, MkANode funcRes) <$
                (newTerm (funcType # FuncType (argR ^# l) funcRes) >>= unify (funcR ^# l))
        where
            l = inferredType (Proxy @expr)
