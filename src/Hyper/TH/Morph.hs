{-# LANGUAGE TemplateHaskellQuotes #-}

module Hyper.TH.Morph
    ( makeHMorph
    ) where

import qualified Control.Lens as Lens
import qualified Data.Map as Map
import           Hyper.Class.Morph
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Hyper.Internal.Prelude

makeHMorph :: Name -> DecsQ
makeHMorph typeName = makeTypeInfo typeName >>= makeHMorphForType

makeHMorphForType :: TypeInfo -> DecsQ
makeHMorphForType info =
    -- TODO: Contexts
    instanceD (pure []) (conT ''HMorph `appT` pure src `appT` pure dst)
    [ D.tySynInstDCompat
        ''MorphConstraint
        (Just [pure (PlainTV constraintVar)])
        ([src, dst, VarT constraintVar] <&> pure)
        (simplifyContext morphConstraint <&> toTuple)
    , DataInstD [] Nothing
        (ConT ''MorphWitness `AppT` WildCardT `AppT` WildCardT `AppT` WildCardT `AppT` WildCardT)
        Nothing (witnesses ^.. traverse . Lens._2) []
        & pure
    , funD 'morphMap (tiConstructors info <&> pure . mkMorphCon)
    , funD 'morphLiftConstraint (liftConstraintClauses <&> pure)
    ]
    <&> (:[])
    where
        (s0, s1) = paramSubsts info
        src = D.applySubstitution s0 (tiInstance info)
        dst = D.applySubstitution s1 (tiInstance info)
        constraintVar = mkName "constraint"
        contents = childrenTypes info
        morphConstraint =
            (tcChildren contents ^.. Lens.folded <&> appSubsts (VarT constraintVar))
            <> (tcEmbeds contents ^.. Lens.folded <&>
                \x -> ConT ''MorphConstraint `appSubsts` x `AppT` VarT constraintVar)
        appSubsts x t = x `AppT` D.applySubstitution s0 t `AppT` D.applySubstitution s1 t
        witnesses =
            -- TODO: Embeds
            tcChildren contents ^.. Lens.folded
            <&>
            ( \x ->
                let n = "M_" <> niceName (tiName info) <> "_" <> mkNiceTypeName x & mkName
                in
                ( x
                , (n, GadtC [n] [] (ConT ''MorphWitness `AppT` src `AppT` dst `appSubsts` x))
                )
            ) & Map.fromList
        liftConstraintClauses
            | Map.null witnesses = [Clause [] (NormalB (LamCaseE [])) []]
            | otherwise = witnesses ^.. traverse . Lens._1 <&> mkLiftConstraint
        mkLiftConstraint n = Clause [ConP n [], WildP] (NormalB (VarE 'id)) []
        mkMorphCon con =
            Clause [VarP varF, p] b []
            where
                (p, b) = morphCon 0 witnesses con

varF :: Name
varF = mkName "_f"

morphCon :: Int -> Map Type (Name, Con) -> (Name, a, [Either b CtrTypePattern]) -> (Pat, Body)
morphCon i witnesses (n, _, fields) =
    ( ConP n (cVars <&> VarP)
    , NormalB (foldl AppE (ConE n) (zipWith bodyFor fields cVars))
    )
    where
        cVars =
            [i ..] <&> show <&> ('x':) <&> mkName
            & take (length fields)
        bodyFor Left{} v = VarE v
        bodyFor (Right x) v = bodyForPat x `AppE` VarE v
        bodyForPat (Node x) = VarE varF `AppE` ConE (witnesses ^?! Lens.ix x . Lens._1)
        bodyForPat (InContainer _ pat) = VarE 'fmap `AppE` bodyForPat pat
        bodyForPat (FlatEmbed x) =
            LamCaseE
            (tiConstructors x
                <&> morphCon (i + length cVars) witnesses
                <&> \(p, b) -> Match p b []
            )
        bodyForPat GenEmbed{} = error "TODO morphCon support for GenEmbed"

type MorphSubsts = (Map Name Type, Map Name Type)

paramSubsts :: TypeInfo -> MorphSubsts
paramSubsts info =
    (tiParams info <&> D.tvName) ^. traverse . Lens.to mkInfo
    where
        pinned = pinnedParams info
        mkInfo name
            | pinned ^. Lens.contains name = mempty
            | otherwise = (side name "0", side name "1")
        side name suffix = mempty & Lens.at name ?~ VarT (mkName (nameBase name <> suffix))

pinnedParams :: TypeInfo -> Set Name
pinnedParams = (^. Lens.to tiConstructors . traverse . Lens._3 . traverse . Lens.to ctrPinnedParams)

ctrPinnedParams :: Either Type CtrTypePattern -> Set Name
ctrPinnedParams (Left t) = typeParams t
ctrPinnedParams (Right Node{}) = mempty
ctrPinnedParams (Right GenEmbed{}) = mempty
ctrPinnedParams (Right (FlatEmbed info)) = pinnedParams info
ctrPinnedParams (Right (InContainer c p)) = typeParams c <> ctrPinnedParams (Right p)

typeParams :: Type -> Set Name
typeParams (VarT x) = mempty & Lens.contains x .~ True
typeParams (AppT f x) = typeParams f <> typeParams x
typeParams (InfixT x _ y) = typeParams x <> typeParams y
-- TODO: Missing cases
typeParams _ = mempty
