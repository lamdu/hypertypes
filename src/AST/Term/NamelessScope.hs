-- | A 'Knot' based implementation of "locally-nameless" terms,
-- inspired by the [bound](http://hackage.haskell.org/package/bound) library
-- and the technique from Bird & Paterson's
-- ["de Bruijn notation as a nested datatype"](https://www.semanticscholar.org/paper/De-Bruijn-Notation-as-a-Nested-Datatype-Bird-Paterson/254b3b01651c5e325d9b3cd15c106fbec40e53ea)

{-# LANGUAGE UndecidableInstances, GeneralizedNewtypeDeriving, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, TemplateHaskell, EmptyCase, GADTs #-}

module AST.Term.NamelessScope
    ( Scope(..), _Scope, KWitness(..)
    , ScopeVar(..), _ScopeVar
    , EmptyScope
    , DeBruijnIndex(..)
    , ScopeTypes(..), _ScopeTypes, HasScopeTypes(..)
    ) where

import           AST
import           AST.Class.Infer.Infer1
import           AST.Infer
import           AST.Term.FuncType
import           AST.Unify (Unify(..), UVarOf)
import           AST.Unify.New (newUnbound)
import           Control.Lens (Lens', Prism')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad.Reader (MonadReader, local)
import           Data.Constraint
import           Data.Sequence (Seq)
import qualified Data.Sequence as Sequence
import           Data.Proxy (Proxy(..))

import           Prelude.Compat

data EmptyScope

newtype Scope expr a k = Scope (Node k (expr (Maybe a)))
Lens.makePrisms ''Scope

newtype ScopeVar (expr :: * -> Knot -> *) a (k :: Knot) = ScopeVar a
Lens.makePrisms ''ScopeVar

makeZipMatch ''Scope
makeKTraversableApplyAndBases ''Scope
makeZipMatch ''ScopeVar
makeKTraversableApplyAndBases ''ScopeVar

class DeBruijnIndex a where
    deBruijnIndex :: Prism' Int a

instance DeBruijnIndex EmptyScope where
    deBruijnIndex = Lens.prism (\case{}) Left

instance DeBruijnIndex a => DeBruijnIndex (Maybe a) where
    deBruijnIndex =
        Lens.prism' toInt fromInt
        where
            toInt Nothing = 0
            toInt (Just x) = 1 + deBruijnIndex # x
            fromInt x
                | x == 0 = Just Nothing
                | otherwise = (x - 1) ^? deBruijnIndex <&> Just

newtype ScopeTypes t v = ScopeTypes (Seq (Node v t))
    deriving newtype (Semigroup, Monoid)

Lens.makePrisms ''ScopeTypes
makeKTraversableApplyAndBases ''ScopeTypes

-- TODO: Replace this class with ones from Infer
class HasScopeTypes v t env where
    scopeTypes :: Lens' env (Tree (ScopeTypes t) v)

instance HasScopeTypes v t (Tree (ScopeTypes t) v) where
    scopeTypes = id

type instance InferOf (Scope t k) = FuncType (TypeOf (t k))
type instance InferOf (ScopeVar t k) = ANode (TypeOf (t k))

instance HasTypeOf1 t => HasInferOf1 (Scope t) where
    type InferOf1 (Scope t) = FuncType (TypeOf1 t)
    type InferOf1IndexConstraint (Scope t) = DeBruijnIndex
    hasInferOf1 p =
        withDict (typeAst (p0 p)) Dict
        where
            p0 :: Proxy (Scope t k) -> Proxy (t k)
            p0 _ = Proxy

instance
    ( Infer1 m t
    , HasInferOf1 t
    , InferOf1IndexConstraint t ~ DeBruijnIndex
    , DeBruijnIndex k
    , Unify m (TypeOf (t k))
    , MonadReader env m
    , HasScopeTypes (UVarOf m) (TypeOf (t k)) env
    , HasInferredType (t k)
    ) =>
    Infer m (Scope t k) where

    inferBody (Scope x) =
        withDict (hasInferOf1 (Proxy @(t k))) $
        withDict (hasInferOf1 (Proxy @(t (Maybe k)))) $
        do
            varType <- newUnbound
            inferChild x
                & local (scopeTypes . _ScopeTypes %~ (varType Sequence.<|))
                <&>
                \(InferredChild xI xR) ->
                ( Scope xI
                , FuncType varType (xR ^# inferredType (Proxy @(t k)))
                )
        \\ (inferMonad :: DeBruijnIndex (Maybe k) :- Infer m (t (Maybe k)))

    inferContext _ _ =
        Dict \\ inferMonad @m @t @(Maybe k)

instance
    ( MonadReader env m
    , HasScopeTypes (UVarOf m) (TypeOf (t k)) env
    , DeBruijnIndex k
    , Unify m (TypeOf (t k))
    ) =>
    Infer m (ScopeVar t k) where

    inferBody (ScopeVar v) =
        Lens.view (scopeTypes . _ScopeTypes)
        <&> (^?! Lens.ix (deBruijnIndex # v))
        <&> MkANode
        <&> (ScopeVar v, )
