{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HFunctor' instances via @TemplateHaskell@
module Hyper.TH.Functor
    ( makeHFunctor
    ) where

import qualified Control.Lens as Lens
import Hyper.Class.Functor (HFunctor (..))
import Hyper.TH.Internal.Utils
import Language.Haskell.TH
import Language.Haskell.TH.Datatype (ConstructorVariant)

import Hyper.Internal.Prelude

-- | Generate a 'HFunctor' instance
makeHFunctor :: Name -> DecsQ
makeHFunctor typeName = makeTypeInfo typeName >>= makeHFunctorForType

makeHFunctorForType :: TypeInfo -> DecsQ
makeHFunctorForType info =
    instanceD
        (makeContext info >>= simplifyContext)
        [t|HFunctor $(pure (tiInstance info))|]
        [ InlineP 'hmap Inline FunLike AllPhases & PragmaD & pure
        , funD 'hmap (tiConstructors info <&> makeCtr)
        ]
        <&> (: [])
    where
        (_, wit) = makeNodeOf info
        makeCtr ctr =
            clause [varP varF, pat] body []
            where
                (pat, body) = makeHMapCtr 0 wit ctr

varF :: Name
varF = mkName "_f"

makeContext :: TypeInfo -> Q [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right
        & traverse ctxForPat
        <&> mconcat
    where
        ctxForPat (InContainer t pat) = (:) <$> [t|Functor $(pure t)|] <*> ctxForPat pat
        ctxForPat (GenEmbed t) = [t|HFunctor $(pure t)|] <&> (: [])
        ctxForPat (FlatEmbed t) = makeContext t
        ctxForPat _ = pure []

makeHMapCtr :: Int -> NodeWitnesses -> (Name, ConstructorVariant, [Either Type CtrTypePattern]) -> (Q Pat, Q Body)
makeHMapCtr i wit (cName, _, cFields) =
    (conP cName (cVars <&> varP), body)
    where
        cVars =
            [i ..]
                <&> mkName . ('x' :) . show
                & take (length cFields)
        body =
            zipWith bodyFor cFields cVars
                & foldl appE (conE cName)
                & normalB
        bodyFor (Right x) v = bodyForPat x `appE` varE v
        bodyFor Left{} v = varE v
        f = varE varF
        bodyForPat (Node t) = [|$f $(nodeWit wit t)|]
        bodyForPat (GenEmbed t) = [|hmap ($f . $(embedWit wit t))|]
        bodyForPat (InContainer _ pat) = [|fmap $(bodyForPat pat)|]
        bodyForPat (FlatEmbed x) =
            lamCaseE
                ( tiConstructors x
                    <&> uncurry match
                        . makeHMapCtr (i + length cVars) wit
                        ?? []
                )
