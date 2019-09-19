{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KFunctor' instances via @TemplateHaskell@

module AST.TH.Functor
    ( makeKFunctor
    ) where

import           AST.Class.Functor
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Prelude.Compat

-- | Generate a 'KFunctor' instance
makeKFunctor :: Name -> DecsQ
makeKFunctor typeName = makeTypeInfo typeName >>= makeKFunctorForType

makeKFunctorForType :: TypeInfo -> DecsQ
makeKFunctorForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFunctor) (pure (tiInstance info)))
    [ InlineP 'mapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapK (tiCons info <&> pure . makeMapKCtr wit (tiVar info))
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiCons info
    >>= D.constructorFields
    <&> matchType (tiVar info)
    >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Functor `AppT` t) : ctxForPat pat
        ctxForPat (Embed t) = [ConT ''KFunctor `AppT` t]
        ctxForPat _ = []

makeMapKCtr :: NodeWitnesses -> Name -> D.ConstructorInfo -> Clause
makeMapKCtr wit knot info =
    Clause [VarP varF, ConP (D.constructorName info) (cVars <&> VarP)] body []
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
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t
        bodyForPat (Embed t) = VarE 'mapK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
        bodyForPat (InContainer _ pat) = bodyForPat pat & AppE (VarE 'fmap)
        bodyForPat PlainData{} = VarE 'id
