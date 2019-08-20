{-# LANGUAGE FlexibleInstances, UndecidableInstances, TemplateHaskell, ScopedTypeVariables #-}

module AST.Term.App
    ( App(..), appFunc, appArg
    , appChildren
    ) where

import AST
import AST.Infer
import AST.Term.FuncType
import AST.Unify (Unify, unify)
import AST.Unify.New (newTerm, newUnbound)
import Control.DeepSeq (NFData)
import Control.Lens (Traversal, makeLenses)
import Control.Lens.Operators
import Data.Binary (Binary)
import Data.Proxy (Proxy(..))
import GHC.Generics (Generic)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), maybeParens)

import Prelude.Compat

data App expr k = App
    { _appFunc :: Node k expr
    , _appArg :: Node k expr
    } deriving Generic

makeLenses ''App
makeZipMatch ''App
makeKTraversableApplyAndBases ''App

instance Pretty (Node k expr) => Pretty (App expr k) where
    pPrintPrec lvl p (App f x) =
        pPrintPrec lvl 10 f <+>
        pPrintPrec lvl 11 x
        & maybeParens (p > 10)

-- Type changing traversal.
-- TODO: Could the normal `Children` class support this?
appChildren ::
    Traversal (App t0 f0) (App t1 f1) (Node f0 t0) (Node f1 t1)
appChildren f (App x0 x1) = App <$> f x0 <*> f x1

instance Inferrable e => Inferrable (App e) where
    type InferOf (App e) = ANode (TypeOf e)

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
            InferRes (App funcI argI) (MkANode funcRes) <$
                (newTerm (funcType # FuncType (argR ^# l) funcRes) >>= unify (funcR ^# l))
        where
            l = inferredType (Proxy @expr)

deriving instance Eq   (Node k expr) => Eq   (App expr k)
deriving instance Ord  (Node k expr) => Ord  (App expr k)
deriving instance Show (Node k expr) => Show (App expr k)
instance Binary (Node k expr) => Binary (App expr k)
instance NFData (Node k expr) => NFData (App expr k)
