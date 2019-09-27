{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HFunctor' instances via @TemplateHaskell@

module Hyper.TH.Functor
    ( makeHFunctor
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Hyper.Class.Functor
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH

import           Prelude.Compat

-- | Generate a 'HFunctor' instance
makeHFunctor :: Name -> DecsQ
makeHFunctor typeName = makeTypeInfo typeName >>= makeHFunctorForType

makeHFunctorForType :: TypeInfo -> DecsQ
makeHFunctorForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''HFunctor) (pure (tiInstance info)))
    [ InlineP 'hmap Inline FunLike AllPhases & PragmaD & pure
    , funD 'hmap (tiConstructors info <&> pure . makeCtr)
    ]
    <&> (:[])
    where
        (_, wit) = makeNodeOf info
        makeCtr ctr =
            Clause [VarP varF, pat] body []
            where
                (pat, body) = makeMapHCtr 0 wit ctr

varF :: Name
varF = mkName "_f"

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._2 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer t pat) = (ConT ''Functor `AppT` t) : ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HFunctor `AppT` t]
        ctxForPat _ = []

makeMapHCtr :: Int -> NodeWitnesses -> (Name, [Either Type CtrTypePattern]) -> (Pat, Body)
makeMapHCtr i wit (cName, cFields) =
    (ConP cName (cVars <&> VarP), body)
    where
        cVars =
            [i ..] <&> show <&> ('x':) <&> mkName
            & take (length cFields)
        body =
            zipWith bodyFor cFields cVars
            & foldl AppE (ConE cName)
            & NormalB
        bodyFor (Right x) v = bodyForPat x `AppE` VarE v
        bodyFor Left{} v = VarE v
        bodyForPat (Node t) = VarE varF `AppE` nodeWit wit t
        bodyForPat (GenEmbed t) = VarE 'hmap `AppE` InfixE (Just (VarE varF)) (VarE '(.)) (Just (embedWit wit t))
        bodyForPat (InContainer _ pat) = bodyForPat pat & AppE (VarE 'fmap)
        bodyForPat (FlatEmbed x) =
            LamCaseE
            (tiConstructors x
                <&> makeMapHCtr (i + length cVars) wit
                <&> \(p, b) -> Match p b []
            )
