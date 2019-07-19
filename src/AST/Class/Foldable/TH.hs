{-# LANGUAGE NoImplicitPrelude, TemplateHaskellQuotes #-}

module AST.Class.Foldable.TH
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.Internal.TH
import           Control.Lens.Operators
import qualified Data.Map as Map
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFoldable :: Name -> DecsQ
makeKFoldable typeName = makeTypeInfo typeName >>= makeKFoldableForType

makeKFoldableForType :: TypeInfo -> DecsQ
makeKFoldableForType info =
    do
        childrenInfo <- makeChildrenTypesInfo info
        body <-
            tiCons info
            & traverse (makeCons childrenInfo (tiVar info))
            <&> CaseE (VarE varX)
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
            [ InlineP 'sumC Inline FunLike AllPhases & PragmaD & pure
            , funD 'sumC
                [ Clause
                    [ childrenTypesPat childrenInfo
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
        ctxForPat (Tof t pat) = (ConT ''Foldable `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFoldable `AppT` t]
        ctxForPat _ = []

makeCons :: ChildrenTypesInfo -> Name -> D.ConstructorInfo -> Q Match
makeCons childrenInfo knot cons =
    do
        let bodyForPat (NodeFofX t) =
                case Map.lookup t (varsForChildTypes childrenInfo) of
                Nothing ->
                    "Failed producing sumC for child of type:\n        " <> show t <>
                    "\n    not in:\n        " <> show (varsForChildTypes childrenInfo)
                    & fail
                Just x -> VarE 'runConvertK `AppE` VarE x & pure
            bodyForPat (XofF t) =
                getEmbedVar childrenInfo t
                <&> \x -> VarE 'sumC `AppE` VarE x
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
            bodyForPat Other{} = VarE 'const `AppE` VarE 'mempty & pure
        let f (typ, name) = bodyForPat (matchType knot typ) <&> (`AppE` VarE name)
        fields <- traverse f consVars
        Match (consPat cons consVars)
            (NormalB (foldl (\x y -> VarE '(<>) `AppE` x `AppE` y) (VarE 'mempty) fields)) []
            & pure
    where
        consVars = makeConstructorVars "x" cons
