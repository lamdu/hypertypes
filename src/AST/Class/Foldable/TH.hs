{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes #-}

module AST.Class.Foldable.TH
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.Internal.TH
import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFoldable :: Name -> DecsQ
makeKFoldable typeName = makeTypeInfo typeName >>= makeKFoldableForType

makeKFoldableForType :: TypeInfo -> DecsQ
makeKFoldableForType info =
    do
        childrenTypes <- getChildrenTypes info
        (childrenCons, childrenSubst) <- getChildrenTypesInfo childrenTypes
        let childrenConsVars = makeConstructorVars "c" childrenCons
        body <-
            tiCons info
            & traverse (makeCons childrenCons childrenSubst childrenConsVars (tiVar info))
            <&> CaseE (VarE varX)
        instanceD (pure (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
            [ InlineP 'sumC Inline FunLike AllPhases & PragmaD & pure
            , funD 'sumC
                [ Clause
                    [ consPat childrenCons childrenConsVars
                    , VarP varX
                    ] (NormalB body) []
                    & pure
                ]
            ]
            <&> (:[])

varX :: Name
varX = mkName "_x"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = [ConT ''Foldable `AppT` t | isPolymorphic t] <> ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFoldable `AppT` t | isPolymorphic t]
        ctxForPat _ = []

makeCons ::
    D.ConstructorInfo -> Map Name Type -> [(Type, Name)] ->
    Name -> D.ConstructorInfo ->
    Q Match
makeCons _childrenCons childrenSubst childrenConsVars knot cons =
    do
        let bodyForPat (NodeFofX t) =
                case Map.lookup t directChildVars of
                Nothing ->
                    "Failed producing sumC for child of type:\n        " <> show t <>
                    "\n    not in:\n        " <> show directChildVars
                    & fail
                Just x -> VarE 'runConvertK `AppE` VarE x & pure
            bodyForPat (XofF t) =
                case Map.lookup t embedChildVars of
                Nothing ->
                    "Failed producing sumS for embedded type:\n        " <> show t <>
                    "\n    not in:\n        " <> show embedChildVars
                    & fail
                Just x -> VarE 'sumC `AppE` VarE x & pure
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
            bodyForPat Other{} = VarE 'const `AppE` VarE 'mempty & pure
        let f (typ, name) = bodyForPat (matchType knot typ) <&> (`AppE` VarE name)
        fields <- traverse f consVars
        Match (consPat cons consVars)
            (NormalB (foldl (\x y -> VarE '(<>) `AppE` x `AppE` y) (VarE 'mempty) fields)) []
            & pure
    where
        consVars = makeConstructorVars "x" cons
        (directChildVars, embedChildVars) = getChildTypeVars childrenConsVars childrenSubst
