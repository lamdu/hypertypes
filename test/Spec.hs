{-# LANGUAGE StandaloneDeriving, UndecidableInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell #-}

import Control.Lens
import Control.Monad.State
import Control.Monad.Error.Class
import Data.IntMap
import Data.Maybe
import Data.Tree.Diverse
import Data.Tree.Diverse.Unification

data Typ f
    = TInt
    | TFun (Node f Typ) (Node f Typ)
    | TRow (Row f)

data Row f
    = REmpty
    | RExtend String (Node f Typ) (Node f Row)

deriving instance (Show (f (Typ f)), Show (Row f)) => Show (Typ f)
deriving instance (Show (f (Typ f)), Show (f (Row f))) => Show (Row f)

data InferState = InferState
    { _typBindings :: IntMap (Typ (UTerm Int))
    , _rowBindings :: IntMap (Row (UTerm Int))
    }
makeLenses ''InferState

newtype InferM a = InferM (StateT InferState Maybe a)
    deriving (Functor, Applicative, Monad, MonadError (), MonadState InferState)

typ :: Node Identity Typ
typ =
    Identity REmpty
    & RExtend "hello" (Identity TInt) & TRow & Identity
    & TFun (Identity TInt) & Identity

instance UnifyMonad Int Typ InferM where
    bindVar k v = typBindings . at k ?= v
    lookupVar k = use (typBindings . at k) <&> fromMaybe (error "var not found")
    unifyBody TInt TInt = pure ()
    unifyBody (TFun a0 r0) (TFun a1 r1) = unify a0 a1 *> unify r0 r1
    unifyBody (TRow r0) (TRow r1) = unifyBody r0 r1
    unifyBody _ _ = throwError ()

instance UnifyMonad Int Row InferM where
    bindVar k v = rowBindings . at k ?= v
    lookupVar k = use (rowBindings . at k) <&> fromMaybe (error "var not found")
    unifyBody REmpty REmpty = pure ()
    unifyBody (RExtend k0 v0 r0) (RExtend k1 v1 r1)
        | k0 == k1 = unify v0 v1 *> unify r0 r1
    unifyBody _ _ = throwError ()

main :: IO ()
main =
    do
        putStrLn ""
        print typ
