{-# LANGUAGE TemplateHaskellQuotes #-}

-- | Generate 'HNodes' instances via @TemplateHaskell@

module Hyper.TH.Nodes
    ( makeHNodes
    ) where

import qualified Control.Lens as Lens
import qualified Data.Set as Set
import           GHC.Generics (V1)
import           Hyper.Class.Nodes
import           Hyper.TH.Internal.Utils
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import           Hyper.Internal.Prelude

-- | Generate a 'HNodes' instance
makeHNodes :: Name -> DecsQ
makeHNodes typeName = makeTypeInfo typeName >>= makeHNodesForType

makeHNodesForType :: TypeInfo -> DecsQ
makeHNodesForType info =
    instanceD (simplifyContext (makeContext info)) (appT (conT ''HNodes) (pure (tiInstance info)))
    [ D.tySynInstDCompat
        ''HNodesConstraint
        (Just [pure (PlainTV constraintVar)])
        ([tiInstance info, VarT constraintVar] <&> pure)
        (simplifyContext nodesConstraint <&> toTuple)
    , D.tySynInstDCompat ''HWitnessType Nothing [pure (tiInstance info)] (pure witType)
    , InlineP 'hLiftConstraint Inline FunLike AllPhases & PragmaD & pure
    , funD 'hLiftConstraint (makeHLiftConstraints wit <&> pure)
    ]
    <&> (:[]) <&> (witDecs <>)
    where
        (witType, witDecs)
            | null nodeOfCons = (ConT ''V1, [])
            | otherwise =
                ( t
                , [DataD [] witTypeName
                    (tiParams info <> [PlainTV (mkName "node")])
                    Nothing (nodeOfCons ?? witType) []
                    ]
                )
            where
                witTypeName = mkName ("W_" <> niceName (tiName info))
                t = tiParams info <&> VarT . D.tvName & foldl AppT (ConT witTypeName)
        (nodeOfCons, wit) = makeNodeOf info
        constraintVar :: Name
        constraintVar = mkName "constraint"
        contents = childrenTypes info
        nodesConstraint =
            (Set.toList (tcChildren contents) <&> (VarT constraintVar `AppT`))
            <> (Set.toList (tcEmbeds contents) <&>
                \x -> ConT ''HNodesConstraint `AppT` x `AppT` VarT constraintVar)
            <> Set.toList (tcOthers contents)

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer _ pat) = ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HNodes `AppT` t]
        ctxForPat _ = []

makeHLiftConstraints :: NodeWitnesses -> [Clause]
makeHLiftConstraints wit
    | null clauses = [Clause [] (NormalB (LamCaseE [])) []]
    | otherwise = clauses
    where
        clauses = (nodeWitCtrs wit <&> liftNode) <> (embedWitCtrs wit <&> liftEmbed)
        liftNode x =
            Clause [ConP 'HWitness [ConP x []]]
            (NormalB (VarE 'const `AppE` VarE 'id)) []
        liftEmbed x =
            Clause [ConP 'HWitness [ConP x [VarP witVar]]]
            (NormalB (VarE 'hLiftConstraint `AppE` VarE witVar)) []
        witVar :: Name
        witVar = mkName "witness"
