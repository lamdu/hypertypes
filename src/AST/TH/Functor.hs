{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KFunctor' instances via @TemplateHaskell@

module AST.TH.Functor
    ( makeKFunctor
    ) where

import           AST.Class.Functor
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'KFunctor' instance
makeKFunctor :: Name -> DecsQ
makeKFunctor typeName = makeTypeInfo typeName >>= makeKFunctorForType

makeKFunctorForType :: TypeInfo -> DecsQ
makeKFunctorForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''KFunctor) (pure (tiInstance info)))
    [ InlineP 'mapK Inline FunLike AllPhases & PragmaD & pure
    , funD 'mapK (tiConstructors info <&> pure . makeMapKCtr wit)
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info >>= snd >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Functor `AppT` t) : ctxForPat pat
        ctxForPat (Embed t) = [ConT ''KFunctor `AppT` t]
        ctxForPat _ = []

makeMapKCtr :: NodeWitnesses -> (Name, [CtrTypePattern]) -> Clause
makeMapKCtr wit (cName, cFields) =
    Clause [VarP varF, ConP cName (cVars <&> VarP)] body []
    where
        varF = mkName "_f"
        cVars =
            [0::Int ..] <&> show <&> ('x':) <&> mkName
            & take (length cFields)
        body =
            zipWith AppE
            (cFields <&> bodyForPat)
            (cVars <&> VarE)
            & foldl AppE (ConE cName)
            & NormalB
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t
        bodyForPat (Embed t) = VarE 'mapK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
        bodyForPat (InContainer _ pat) = bodyForPat pat & AppE (VarE 'fmap)
        bodyForPat PlainData{} = VarE 'id
