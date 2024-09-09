{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Generate 'HNodes' instances via @TemplateHaskell@
module Hyper.TH.Nodes
    ( makeHNodes
    ) where

import qualified Control.Lens as Lens
import GHC.Generics (V1)
import Hyper.Class.Nodes (HNodes (..), HWitness (..))
import Hyper.TH.Internal.Utils
import Language.Haskell.TH
import qualified Language.Haskell.TH.Datatype as D

import Hyper.Internal.Prelude

-- | Generate a 'HNodes' instance
makeHNodes :: Name -> DecsQ
makeHNodes typeName = makeTypeInfo typeName >>= makeHNodesForType

makeHNodesForType :: TypeInfo -> DecsQ
makeHNodesForType info =
    [ instanceD
        (simplifyContext (makeContext info))
        [t|HNodes $(pure (tiInstance info))|]
        [ D.tySynInstDCompat
            ''HNodesConstraint
            (Just [pure (plainTV constraintVar)])
            [pure (tiInstance info), c]
            (nodesConstraint >>= simplifyContext <&> toTuple)
        , D.tySynInstDCompat ''HWitnessType Nothing [pure (tiInstance info)] witType
        , InlineP 'hLiftConstraint Inline FunLike AllPhases & PragmaD & pure
        , funD 'hLiftConstraint (makeHLiftConstraints wit)
        ]
    ]
        <> witDecs
        & sequenceA
    where
        (witType, witDecs)
            | null nodeOfCons = ([t|V1|], [])
            | otherwise =
                ( tiParams info <&> varT . D.tvName & foldl appT (conT witTypeName)
                ,
                    [ dataD
                        (pure [])
                        witTypeName
                        (((BndrReq <$) <$> tiParams info) <> [plainTV (mkName "node")])
                        Nothing
                        (nodeOfCons <&> (witType >>=))
                        []
                    ]
                )
            where
                witTypeName = mkName ("W_" <> niceName (tiName info))
        (nodeOfCons, wit) = makeNodeOf info
        constraintVar = mkName "constraint"
        c = varT constraintVar
        contents = childrenTypes info
        nodesConstraint =
            (tcChildren contents ^.. Lens.folded <&> (c `appT`) . pure)
                <> (tcEmbeds contents ^.. Lens.folded <&> \x -> [t|HNodesConstraint $(pure x) $c|])
                <> (tcOthers contents ^.. Lens.folded <&> pure)
                & sequenceA

makeContext :: TypeInfo -> [Pred]
makeContext info =
    tiConstructors info ^.. traverse . Lens._3 . traverse . Lens._Right >>= ctxForPat
    where
        ctxForPat (InContainer _ pat) = ctxForPat pat
        ctxForPat (GenEmbed t) = [ConT ''HNodes `AppT` t]
        ctxForPat (FlatEmbed t) = makeContext t
        ctxForPat _ = []

makeHLiftConstraints :: NodeWitnesses -> [Q Clause]
makeHLiftConstraints wit
    | null clauses = [clause [] (normalB [|\case {}|]) []]
    | otherwise = clauses
    where
        clauses = (nodeWitCtrs wit <&> liftNode) <> (embedWitCtrs wit <&> liftEmbed)
        liftNode x = clause [conP 'HWitness [conP x []]] (normalB [|\_ r -> r|]) []
        liftEmbed x =
            clause
                [conP 'HWitness [conP x [varP witVar]]]
                (normalB [|hLiftConstraint $(varE witVar)|])
                []
        witVar :: Name
        witVar = mkName "witness"
