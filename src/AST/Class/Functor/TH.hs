{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes #-}

module AST.Class.Functor.TH
    ( makeKFunctor
    ) where

import           AST.Class.Functor
import           AST.Internal.TH
import           Control.Lens.Operators
import qualified Data.Map as Map
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFunctor :: Name -> DecsQ
makeKFunctor typeName = makeTypeInfo typeName >>= makeKFunctorForType

makeKFunctorForType :: TypeInfo -> DecsQ
makeKFunctorForType info =
    do
        childrenTypesInfo <- makeChildrenTypesInfo info
        body <-
            tiCons info
            & traverse (makeCons childrenTypesInfo (tiVar info))
            <&> CaseE (VarE varX)
        instanceD (pure (makeContext info)) (appT (conT ''KFunctor) (pure (tiInstance info)))
            [ InlineP 'mapC Inline FunLike AllPhases & PragmaD & pure
            , funD 'mapC
                [ Clause
                    [ childrenTypesPat childrenTypesInfo
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
        ctxForPat (Tof t pat) = [ConT ''Functor `AppT` t | isPolymorphicContainer t] <> ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFunctor `AppT` t | isPolymorphic t]
        ctxForPat _ = []

makeCons :: ChildrenTypesInfo -> Name -> D.ConstructorInfo -> Q Match
makeCons childrenInfo knot cons =
    do
        let bodyForPat (NodeFofX t) =
                case Map.lookup t (varsForChildTypes (childrenTypesVars childrenInfo)) of
                Nothing ->
                    "Failed producing mapC for child of type:\n        " <> show t <>
                    "\n    not in:\n        " <> show (varsForChildTypes (childrenTypesVars childrenInfo))
                    & fail
                Just x -> VarE 'runMapK `AppE` VarE x & pure
            bodyForPat (XofF t) =
                getEmbedTypeVar (childrenTypesVars childrenInfo) t
                <&> \x -> VarE 'mapC `AppE` VarE x
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'fmap)
            bodyForPat Other{} = VarE 'id & pure
        let f (typ, name) = bodyForPat (matchType knot typ) <&> (`AppE` VarE name)
        fields <- traverse f consVars
        Match (consPat cons consVars)
            (NormalB (foldl AppE (ConE (D.constructorName cons)) fields)) []
            & pure
    where
        consVars = makeConstructorVars "x" cons