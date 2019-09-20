{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'KPointed' instances via @TemplateHaskell@

module AST.TH.Pointed
    ( makeKPointed
    ) where

import           AST.Class.Pointed
import           AST.TH.Internal.Utils
import           Control.Lens.Operators
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'KPointed' instance
makeKPointed :: Name -> DecsQ
makeKPointed typeName = makeTypeInfo typeName >>= makeKPointedForType

makeKPointedForType :: TypeInfo -> DecsQ
makeKPointedForType info =
    do
        cons <-
            case tiConstructors info of
            [x] -> pure x
            _ -> fail "makeKPointed only supports types with a single constructor"
        instanceD (simplifyContext (makeContext info)) (appT (conT ''KPointed) (pure (tiInstance info)))
            [ InlineP 'pureK Inline FunLike AllPhases & PragmaD & pure
            , funD 'pureK [makePureKCtr info cons & pure]
            ]
    <&> (:[])

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info >>= snd >>= ctxFor
    where
        ctxFor (Right x) = ctxForPat x
        ctxFor (Left x) = [ConT ''Monoid `AppT` x]
        ctxForPat (InContainer t pat) = (ConT ''Applicative `AppT` t) : ctxForPat pat
        ctxForPat (Embed t) = [ConT ''KPointed `AppT` t]
        ctxForPat _ = []

makePureKCtr :: TypeInfo -> (Name, [Either Type CtrTypePattern]) -> Clause
makePureKCtr typeInfo (cName, cFields) =
    Clause [VarP varF] body []
    where
        body =
            cFields
            <&> bodyFor
            & foldl AppE (ConE cName)
            & NormalB
        bodyFor (Right x) = bodyForPat x
        bodyFor Left{} = VarE 'mempty
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t
        bodyForPat (Embed t) = VarE 'pureK `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
        bodyForPat (InContainer _ pat) = bodyForPat pat & AppE (VarE 'pure)
        varF = mkName "_f"
        (_, wit) = makeNodeOf typeInfo
