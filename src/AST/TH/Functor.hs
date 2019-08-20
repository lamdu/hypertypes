{-# LANGUAGE TemplateHaskellQuotes #-}

module AST.TH.Functor
    ( makeKFunctor
    ) where

import           AST.Class
import           AST.TH.Internal
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

makeKFunctor :: Name -> DecsQ
makeKFunctor typeName = makeTypeInfo typeName >>= makeKFunctorForType

makeKFunctorForType :: TypeInfo -> DecsQ
makeKFunctorForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFunctor) (pure (tiInstance info)))
    [ InlineP 'mapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapK (tiCons info <&> pure . makeMapKCtr [] (VarE 'mapK) (tiVar info))
    , InlineP 'mapKWith Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapKWith (tiCons info <&> pure . makeMapKCtr [VarP proxy] (VarE 'mapKWith `AppE` VarE proxy) (tiVar info))
    ]
    <&> (:[])
    where
        proxy = mkName "_p"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (Tof t pat) = (ConT ''Functor `AppT` t) : ctxForPat pat
        ctxForPat (XofF t) = [ConT ''KFunctor `AppT` t]
        ctxForPat _ = []

makeMapKCtr :: [Pat] -> Exp -> Name -> D.ConstructorInfo -> Clause
makeMapKCtr patBase inner knot info =
    Clause (patBase <> [VarP varF, ConP (D.constructorName info) (cVars <&> VarP)]) body []
    where
        varF = mkName "_f"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length (D.constructorFields info))
        body =
            zipWith AppE
            (pats <&> bodyForPat)
            (cVars <&> VarE)
            & foldl AppE (ConE (D.constructorName info))
            & NormalB
        pats = D.constructorFields info <&> matchType knot
        bodyForPat NodeFofX{} = VarE varF
        bodyForPat XofF{} = inner `AppE` VarE varF
        bodyForPat (Tof _ pat) = bodyForPat pat & AppE (VarE 'fmap)
        bodyForPat Other{} = VarE 'id
