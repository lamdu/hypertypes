{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Foldable
    ( makeKFoldable
    ) where

import           AST.Class.Foldable
import           AST.Combinator.ANode (ANode(..))
import           AST.TH.Internal
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
        childrenInfo <- makeNodeTypesInfo info
        body <-
            tiCons info
            & traverse (makeCons childrenInfo (tiVar info))
            <&> CaseE (VarE varX)
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KFoldable) (pure (tiInstance info)))
            [ InlineP 'foldMapC Inline FunLike AllPhases & PragmaD & pure
            , funD 'foldMapC
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

makeCons :: NodeTypesInfo -> Name -> D.ConstructorInfo -> Q Match
makeCons childrenInfo knot cons =
    do
        let bodyForPat (NodeFofX t) =
                case Map.lookup t (varsForChildTypes childrenInfo) of
                Just x -> VarE 'runConvertK `AppE` VarE x & pure
                Nothing ->
                    getEmbedTypes childrenInfo (ConT ''ANode `AppT` t)
                    <&> AppE (VarE 'getANode)
                    <&> AppE (VarE 'runConvertK)
            bodyForPat (XofF t) = getEmbedTypes childrenInfo t <&> AppE (VarE 'foldMapC)
            bodyForPat (Tof _ pat) = bodyForPat pat <&> AppE (VarE 'foldMap)
            bodyForPat Other{} = VarE 'const `AppE` VarE 'mempty & pure
        let f (typ, name) = bodyForPat (matchType knot typ) <&> (`AppE` VarE name)
        fields <- traverse f consVars
        Match (consPat cons consVars)
            (NormalB (foldl (\x y -> VarE '(<>) `AppE` x `AppE` y) (VarE 'mempty) fields)) []
            & pure
    where
        consVars = makeConstructorVars "x" cons
