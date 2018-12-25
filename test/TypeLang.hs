{-# LANGUAGE StandaloneDeriving, UndecidableInstances, TemplateHaskell, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, DataKinds, GeneralizedNewtypeDeriving #-}

module TypeLang where

import AST
import AST.Class.Infer
import AST.Class.Instantiate
import AST.Unify
import AST.Unify.IntMapBinding
import AST.Unify.STBinding
import AST.Unify.Term
import AST.Term.FuncType
import AST.Term.Scheme
import AST.Term.Scope
import AST.Term.Var
import Control.Applicative
import Control.Lens (ALens')
import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad.RWS
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST(..))
import Control.Monad.Trans.Maybe
import Data.Map
import Data.Maybe
import Data.STRef

data Typ f
    = TInt
    | TFun (FuncType Typ f)
    | TRow (Row f)
    | TVar String

data Row f
    = REmpty
    | RExtend String (Tie f Typ) (Tie f Row)
    | RVar String

data Types f = Types
    { _tTyp :: Tie f Typ
    , _tRow :: Tie f Row
    }

Lens.makePrisms ''Typ
Lens.makePrisms ''Row
Lens.makeLenses ''Types
makeChildrenAndZipMatch [''Typ, ''Row, ''Types]

deriving instance SubTreeConstraint Typ f Show => Show (Typ f)
deriving instance SubTreeConstraint Row f Show => Show (Row f)

instance HasChild Types Typ where getChild = tTyp
instance HasChild Types Row where getChild = tRow

type IntInferState = (Tree Types IntBindingState, Tree Types (Const Int))

emptyIntInferState :: IntInferState
emptyIntInferState =
    ( Types emptyIntBindingState emptyIntBindingState
    , Types (Const 0) (Const 0)
    )

type instance SchemeType (Tree Pure Typ) = Typ
instance (MonadInfer m, Recursive (Unify m) Typ) => Instantiate m (Tree Pure Typ)

instance HasQuantifiedVar Typ where
    type QVar Typ = String
    quantifiedVar = _TVar

instance HasQuantifiedVar Row where
    type QVar Row = String
    quantifiedVar = _RVar

type IntInfer r w = RWST (r, InferLevel) w IntInferState Maybe

type instance UVar (IntInfer r w) = Const Int

instance Monoid w => MonadInfer (IntInfer r w) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Monoid w => Unify (IntInfer r w) Typ where
    binding = intBindingState (Lens._1 . tTyp)
    newQuantifiedVariable _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Monoid w => Unify (IntInfer r w) Row where
    binding = intBindingState (Lens._1 . tRow)
    newQuantifiedVariable _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show

instance Monoid w => Recursive (Unify (IntInfer r w)) Typ
instance Monoid w => Recursive (Unify (IntInfer r w)) Row
instance Monoid w => Recursive (CanInstantiate (IntInfer r w) Types) Typ
instance Monoid w => Recursive (CanInstantiate (IntInfer r w) Types) Row

type STInferState s = Tree Types (Const (STRef s Int))

type STInfer r s = ReaderT (r, InferLevel, STInferState s) (MaybeT (ST s))

type instance UVar (STInfer r s) = STVar s

readModifySTRef :: STRef s a -> (a -> a) -> ST s (a, a)
readModifySTRef ref func =
    do
        old <- readSTRef ref
        let new = func old
        (old, new) <$ (new `seq` writeSTRef ref new)

newStQuantified ::
    (MonadReader (a, InferLevel, STInferState s) m, MonadST m) =>
    ALens' (STInferState s) (Const (STRef (World m) Int) (ast :: Knot)) -> m Int
newStQuantified l =
    Lens.view (Lens._3 . Lens.cloneLens l . Lens._Wrapped)
    >>= liftST . fmap fst . (`readModifySTRef` (+1))

instance MonadInfer (STInfer r s) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Unify (STInfer r s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified tTyp <&> ('t':) . show

instance Unify (STInfer r s) Row where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified tRow <&> ('r':) . show

instance Recursive (Unify (STInfer r s)) Typ
instance Recursive (Unify (STInfer r s)) Row
instance Recursive (CanInstantiate (STInfer r s) Types) Typ
instance Recursive (CanInstantiate (STInfer r s) Types) Row

instance HasFuncType Typ where
    funcType = _TFun

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x) where
    scopeTypes = Lens._1 . scopeTypes

instance HasScopeTypes v Typ a => HasScopeTypes v Typ (a, x, y) where
    scopeTypes = Lens._1 . scopeTypes

newtype IntInferB v a =
    IntInferB (IntInfer (Map v (IntInferB v (Tree (Const Int) Typ))) () a)
    deriving
    ( Functor, Applicative, Alternative, Monad
    , MonadReader (Map v (IntInferB v (Tree (Const Int) Typ)), InferLevel)
    , MonadState IntInferState
    )

type instance UVar (IntInferB v) = Const Int

instance Ord v => MonadScopeTypes v Typ (IntInferB v) where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadInfer (IntInferB v) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Unify (IntInferB v) Typ where
    binding = intBindingState (Lens._1 . tTyp)
    newQuantifiedVariable _ = increase (Lens._2 . tTyp . Lens._Wrapped) <&> ('t':) . show

instance Unify (IntInferB v) Row where
    binding = intBindingState (Lens._1 . tRow)
    newQuantifiedVariable _ = increase (Lens._2 . tRow . Lens._Wrapped) <&> ('r':) . show

instance Recursive (Unify (IntInferB v)) Typ
instance Recursive (Unify (IntInferB v)) Row
instance Recursive (CanInstantiate (IntInferB v) Types) Typ
instance Recursive (CanInstantiate (IntInferB v) Types) Row

newtype STInferB v s a =
    STInferB (STInfer (Map v (STInferB v s (Tree (STVar s) Typ))) s a)
    deriving
    ( Functor, Applicative, Alternative, Monad, MonadST
    , MonadReader (Map v (STInferB v s (Tree (STVar s) Typ)), InferLevel, STInferState s)
    )

type instance UVar (STInferB v s) = STVar s

instance Ord v => MonadScopeTypes v Typ (STInferB v s) where
    scopeType v = Lens.view (Lens._1 . Lens.at v) >>= fromMaybe (error "name error")
    localScopeType v t = local (Lens._1 . Lens.at v ?~ t)

instance MonadInfer (STInferB v s) where
    getInferLevel = Lens.view Lens._2
    localLevel = local (Lens._2 . _InferLevel +~ 1)

instance Unify (STInferB v s) Typ where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified tTyp <&> ('t':) . show

instance Unify (STInferB v s) Row where
    binding = stBindingState
    newQuantifiedVariable _ = newStQuantified tRow <&> ('r':) . show

instance Recursive (Unify (STInferB v s)) Typ
instance Recursive (Unify (STInferB v s)) Row
instance Recursive (CanInstantiate (STInferB v s) Types) Typ
instance Recursive (CanInstantiate (STInferB v s) Types) Row
