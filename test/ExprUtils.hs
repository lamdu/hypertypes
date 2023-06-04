{-# LANGUAGE FlexibleContexts #-}

module ExprUtils (prettyStyle, forAll, testCommon, addAnns, inferExpr) where

import qualified Control.Lens as Lens
import Control.Lens.Operators
import Control.Monad
import Data.Constraint
import qualified Data.Map as Map
import Hyper
import Hyper.Infer
import Hyper.Recurse
import Hyper.Syntax.Scheme
import Hyper.Unify
import Hyper.Unify.Generalize
import Hyper.Unify.QuantifiedVar
import Test.Tasty
import Test.Tasty.HUnit
import qualified Text.PrettyPrint as Pretty
import Text.PrettyPrint.HughesPJClass (Pretty (..))
import TypeLang

import Prelude

prettyStyle :: Pretty a => a -> String
prettyStyle = Pretty.renderStyle (Pretty.Style Pretty.OneLineMode 0 0) . pPrint

forAll ::
    (Traversable t, Traversable u) =>
    t Name ->
    u Name ->
    (t (HPlain Typ) -> u (HPlain Row) -> HPlain Typ) ->
    Pure # Scheme Types Typ
forAll tvs rvs body =
    _Pure
        # Scheme
            (Types (foralls tvs) (foralls rvs))
            (body (tvs <&> TVarP) (rvs <&> RVarP) ^. hPlain)

foralls ::
    (Foldable f, Monoid (TypeConstraintsOf typ), Ord (QVar typ)) =>
    f (QVar typ) ->
    QVars # typ
foralls xs =
    xs ^.. Lens.folded
        <&> (,mempty)
        & Map.fromList
        & QVars

testCommon ::
    (Pretty (lang # Pure), Pretty a) =>
    Pure # lang ->
    String ->
    Either (TypeError # Pure) a ->
    Either (TypeError # Pure) a ->
    TestTree
testCommon expr expect pureRes stRes =
    do
        assertEqualStrings msg expect (prettyStyle pureRes)
        assertEqualStrings ("ST: " <> msg) expect (prettyStyle stRes)
        & testCase (prettyStyle expr)
    where
        msg = "Infer of " <> prettyStyle expr

assertEqualStrings :: String -> String -> String -> IO ()
assertEqualStrings msg expected value
    | value == expected = pure ()
    | otherwise =
        assertFailure (msg <> "\nexpected: " <> expected <> "\n but got: " <> value)

inferExpr ::
    forall m t.
    ( HasInferredType t
    , Infer m t
    , HasScheme Types m (TypeOf t)
    , RTraversable t
    , Recursively (InferOfConstraint HFoldable) t
    ) =>
    Pure # t ->
    m (Pure # Scheme Types (TypeOf t))
inferExpr x =
    do
        inferRes <- infer (addAnns x)
        result <-
            inferRes ^# hAnn . Lens._2 . _InferResult . inferredType (Proxy @t)
                & generalize
                >>= saveScheme
        result
            <$ htraverse_
                ( Proxy @(Infer m) #*#
                    Proxy @(Recursively (InferOfConstraint HFoldable)) #*#
                        \(w :: HWitness (HFlip Ann t) n) (Const () :*: InferResult i) ->
                            htraverse_ (Proxy @(UnifyGen m) #> void . applyBindings) i
                                \\ inferContext (Proxy @m) w
                                \\ inferOfConstraint @HFoldable w
                                \\ recursively (Proxy @(InferOfConstraint HFoldable n))
                )
                (_HFlip # inferRes)

addAnns :: Recursively HFunctor h => Pure # h -> Ann (Const ()) # h
addAnns = wrap (const (Ann (Const ())))
